module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AhFrameFactorEqNegOnePowRiemannForm
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsTorusOfPeriodHermitian
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaFunctionTorusL2Norm
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqSemilinearLeLatticeFrameNormSq
section
open NumberField
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameCS

theorem norm_sum_sq_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.det ≠ 0) (X lam : Fin N → ℂ) :
    ‖∑ j, X j * lam j‖ ^ 2 ≤ (∑ i, ‖(A⁻¹.mulVec X) i‖ ^ 2) * ∑ a, ‖∑ m, A m a * lam m‖ ^ 2 := by
  set Y := A⁻¹.mulVec X with hY
  have hX : X = A.mulVec Y := by
    rw [hY, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA), Matrix.one_mulVec]
  have e : ∑ j, X j * lam j = ∑ a, Y a * ∑ m, A m a * lam m := by
    rw [hX]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e]
  calc ‖∑ a, Y a * ∑ m, A m a * lam m‖ ^ 2 ≤ (∑ a, ‖Y a‖ * ‖∑ m, A m a * lam m‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (le_of_eq ?_)) 2
        simp only [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end GlobalTheory.FrameCS


open GlobalTheory.FrameCS in
theorem GlobalTheory.frame_semilinear_sq_le : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (N n : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W) (σ : K →+* ℂ) (ℓ : W → ℂ), GlobalTheory.CompHt.IsFrame Nm W b g A → (∀ k, (gw k : V) = ∑ j, g j k • b j) → (∀ j, b j = ∑ k, c k j • (gw k : V)) → (∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ℓ x = ∑ k, σ (β k : K) * ℓ (u k)) → ∀ x : W, ‖ℓ x‖ ^ 2 ≤ Nm σ x ^ 2 * ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k)‖ ^ 2 := by
  intro K V _ _ _ _ _ _ Nm W N n b g A c gw σ ℓ hF hg hc hℓ x
  set lam : Fin N → ℂ := fun j => ∑ k, σ (c k j) * ℓ (gw k) with hlam

  have h2 : ∀ k, ℓ (gw k) = ∑ j, σ (g j k) * lam j := by
    intro k
    set e : Fin n → K := fun l => ∑ j, g j k * c l j with he
    have hexp : (gw k : V) = ∑ l, e l • (gw l : V) := by
      rw [hg k]
      simp_rw [hc, he, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
      (Finset.univ.image e)
    choose β hβ using fun l => hd _ (Finset.mem_image_of_mem e (Finset.mem_univ l))
    have hβ' : ∀ l, ((β l : 𝓞 K) : K) = ((d : 𝓞 K) : K) * e l := fun l => by
      rw [← Algebra.smul_def, ← hβ l]
    have hx1 : (((d : 𝓞 K) • gw k : W) : V) = ∑ l, β l • (gw l : V) := by
      rw [Submodule.coe_smul, ← algebraMap_smul K, hexp, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← algebraMap_smul K (β l), smul_smul]
      congr 1
      exact (hβ' l).symm
    have hx2 : (((d : 𝓞 K) • gw k : W) : V) = ∑ _i : Fin 1, (d : 𝓞 K) • (gw k : V) := by
      simp
    have e1 := hℓ n β gw _ hx1
    have e2 := hℓ 1 (fun _ => (d : 𝓞 K)) (fun _ => gw k) _ hx2
    simp only [Finset.univ_unique, Finset.sum_singleton] at e2
    have hd0 : σ ((d : 𝓞 K) : K) ≠ 0 := by
      rw [map_ne_zero, ne_eq, RingOfIntegers.coe_eq_zero_iff]
      exact nonZeroDivisors.coe_ne_zero d
    apply mul_left_cancel₀ hd0
    rw [← e2, e1]
    simp only [hβ', map_mul, hlam, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [he, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

  have hxmem : (x : V) ∈ Submodule.span (𝓞 K) (Set.range fun k => (gw k : V)) := by
    have := hF.span
    have hfun : (fun k => ∑ j, g j k • b j) = fun k => (gw k : V) := funext fun k => (hg k).symm
    rw [hfun] at this
    rw [this]; exact x.2
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hxmem
  have h3 : ℓ x = ∑ j, σ (b.repr x j) * lam j := by
    rw [hℓ n β gw x hβ.symm]
    have hr : ∀ j, b.repr x j = ∑ k, (β k : K) * g j k := by
      intro j
      have hk : ∀ k, β k • (gw k : V) = ∑ j, ((β k : K) * g j k) • b j := by
        intro k
        rw [← algebraMap_smul K, hg k, Finset.smul_sum]
        simp_rw [smul_smul]
      rw [← hβ, Finset.sum_congr rfl fun k _ => hk k, Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      rw [Module.Basis.repr_sum_self]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hr, h2, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

  have hN : Nm σ x ^ 2 = ∑ i, ‖((A σ)⁻¹.mulVec fun j => σ (b.repr x j)) i‖ ^ 2 := by
    rw [← hF.norm σ x, GlobalTheory.ChowHt.frameNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  have hu : ∀ a, ∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k) = ∑ m, A σ m a * lam m := by
    intro a
    simp only [hlam, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
  simp only [hu, hN, h3]
  exact norm_sum_sq_le (A σ) (hF.herm σ) _ lam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqThetaConstantSpanningClassesLeExp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaConst.ArchBound

theorem norm_pow_le_at_unit_frame (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hA : AllTest Xo c) (R : ℕ) (hR : Odd R)
    (h1R : 1 < R) (xs : Fin r → LatMod Dw (R ^ 4)) (f : Rul Xo c)
    (hsp : Submodule.span (𝓞 E) (Set.range xs) = ⊤)
    (hf : GlobalTheory.ThetaConst.IsTauRule Xo c R (fun _ : Unit => 1) (fun _ => xs) f) (DF q m : ℕ) (R0 : ℝ)
    (hrun : RunOK E r DF q R0 m) (hm : Dw.p ≤ m ∨ Dw.q ≤ m) (k : U.Comp) (x : (U.X k).dom)
    (hx : ∀ τ i, ‖dmin (U.X k).Gm x.1 τ i‖ = 1) :
    ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ^ (2 * R ^ 4) ≤
      Real.exp (-((1 : ℕ) : ℝ) * (I2.phiFD (U.X k) (I2.th (E := E) q R0) x.1 - p16 E r q m R 1)) := by
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r U hU
  obtain ⟨Hm, χl, fr, θ, Fd, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, hFd, hl2⟩ := Uw.norm k x hx
  have hy : (U.un k x).x = Uw.F.u (Uw.ik k) (Uw.Pm k x) := (Uw.lie k x).1
  have hP := Uw.period k x
  have hfn : IsFnOf Uw.F (Uw.ik k) (Uw.Pm k x) fr (U.un k x).x (U.un k x).s θ := a₉
  have hAH : AHFrame Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr :=
    ⟨a₁, a₂, a₃, a₄, a₅, a₆, fun j hj => by rw [← hy]; exact a₇ j hj, a₈⟩
  have hty := (_root_.GlobalTheory.EtaAn.relab_isTypeFn E H Dw l Xo c σ hσ).2.2 Uw.g Uw.e
  have hty' : IsTypeFn H (Uw.F.Di (Uw.ik k)).p (Uw.F.Di (Uw.ik k)).q
      (fun j => Formalism.L2.PjFree.relab c σ (Uw.e j).1) := by
    rw [(Uw.F.sig _).1, (Uw.F.sig _).2]
    exact hty
  obtain ⟨T, ψ, hT⟩ := _root_.GlobalTheory.PeriodTorus.exists_torusOf E H _ _ _ _ Hm hty' hP a₁ a₂ a₃
  obtain ⟨-, hr, hph, hdim⟩ := _root_.GlobalTheory.PeriodTorus.isTorusAt_of_isTorusOf E H Dw l Xo c σ r U hσ hU Uw k x Hm T ψ ⟨a₁, a₂, a₃⟩ hT
  have hhol : Differentiable ℂ θ ∧ ∀ a z, θ (z + Uw.Pm k x a) = χl (Uw.Pm k x a) *
      Complex.exp (Real.pi * hermForm Hm z (Uw.Pm k x a) + Real.pi / 2 * hermForm Hm (Uw.Pm k x a) (Uw.Pm k x a)) *
        θ z := by
    have key : ∀ (x₀ : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x₀)), x₀ = Uw.F.u (Uw.ik k) (Uw.Pm k x) →
        IsFnOf Uw.F (Uw.ik k) (Uw.Pm k x) fr x₀ s θ → Differentiable ℂ θ ∧ ∀ a z, θ (z + Uw.Pm k x a) =
          χl (Uw.Pm k x a) * Complex.exp (Real.pi * hermForm Hm z (Uw.Pm k x a) +
            Real.pi / 2 * hermForm Hm (Uw.Pm k x a) (Uw.Pm k x a)) * θ z := by
      intro x₀ s h₀ hs
      subst h₀
      exact _root_.GlobalTheory.EtaAn.isFnOf_entire_factor E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr hP hAH s θ hs
    exact key _ _ hy hfn
  have hchi := _root_.GlobalTheory.ahFrame_factor_eq_negOnePow E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr hP hAH
  obtain ⟨hsec, hl2', hpt⟩ := _root_.GlobalTheory.EtaAn.ThetaTorus.theta_section_l2_torus E H _ _ _ _ Hm T ψ θ Fd hT hhol.1
    (fun a z => by rw [hhol.2 a z, hchi a]) hFd
  rw [hl2] at hl2'
  have hR4 : 0 < R ^ 4 := pow_pos hR.pos 4

  have hval₀ := hf.tauValAt_evR hR (hA _ (U.un k x))
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨ev, hevL⟩ := GlobalTheory.ThetaConst.exists_isLevOf_geometric Xo c hval₀.dvd (U.un k x).x
  have hev : IsFullLev Xo (R ^ 4) (U.un k x).x ev := hevL.2.1
  obtain ⟨a, ha, hgen⟩ := _root_.GlobalTheory.fullLevel_eq_exp_periods E H Dw l Xo c σ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) (U.un k x) hP hy (R ^ 4) hR4 ev hev
  have hR2 : Odd (R ^ 2) := hR.pow
  have htors : ∀ q, ev q ^ ((R ^ 2) ^ 2) = 1 := fun q => by rw [← pow_mul]; exact (ha q).2
  choose w hw using fun q =>
    ((GlobalTheory.nullValue_existsUnique_natural_linear GlobalTheory.firstFiveLaws.1 E H Dw l Xo c (R ^ 2) hR2).1 _ (U.un k x) (ev q)
      (htors q)).exists
  have hR0 : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hR.pos.ne'
  let z : LatMod Dw (R ^ 4) → (Fin Uw.g → ℂ) := fun q =>
    ((R ^ 2 : ℕ) : ℂ) • ((R ^ 4 : ℕ) : ℂ)⁻¹ • Uw.Pm k x (a q)
  have hz : ∀ q, ((R : ℂ) ^ 2) • ψ (z q) = ψ (Uw.Pm k x (a q)) := fun q => by
    rw [← map_smul]
    congr 1
    simp only [z, smul_smul]
    have : (R : ℂ) ^ 2 * (((R ^ 2 : ℕ) : ℂ) * ((R ^ 4 : ℕ) : ℂ)⁻¹) = 1 := by
      push_cast
      field_simp
    rw [this, one_smul]
  have hwn : ∀ q, ‖Formalism.L2.PjFree.toC (w q)‖ =
      Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) (fun _ => ψ (z q))) := fun q => by
    rw [hpt]
    exact _root_.GlobalTheory.norm_nullVal_eq_norm_theta E H Dw l Xo c σ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr θ (U.un k x) hP hAH hy hfn (R ^ 2) hR2
      (ev q) _ (w q) (htors q) (ha q).1 (hw q)

  have hval : evR Xo c f (U.un k x) = ∏ b, w (xs b) := by
    rw [hval₀.unique hR (GlobalTheory.ThetaConst.tauValAt_self hevL hw), GlobalTheory.ThetaConst.tauExpr]
    simp
  obtain ⟨P, hq, hR0', hm'⟩ := hrun T hr (hdim m hm)
  rw [hval, ← hph, ← hq, ← hR0', ← hm']
  have hgen' : ∀ (g : Fin (2 * R ^ 4)) (j : Unit), ∀ v ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
      v = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • ψ (z (xs b))) + (R : ℂ) • y := fun g j => by
    simp only [hz]
    exact GlobalTheory.EtaAn.ArchPt.gen_mod hP hT R (fun b => a (xs b)) (hgen r _ hsp)
  have hmem : ∀ q, ((R : ℂ) ^ 2) • ψ (z q) ∈ T.L := fun q => by
    rw [hz]
    exact (hT.2.2.2.1 _).2 ⟨_, rfl⟩
  have key : ∀ (r : ℕ), T.r = r → Fintype.card Unit ≤ R ^ (2 * I2.PT.f E * r ^ 2) →
      ∀ (w : Fin (2 * R ^ 4) → Unit → Fin r → ℂ) (a : Fin (2 * R ^ 4) → Unit → Fin r → I2.Vsp T.dim),
      (∀ g j b, ((R : ℂ) ^ 2) • a g j b ∈ T.L) →
      (∀ g j, ∀ x ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
        x = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • a g j b) + (R : ℂ) • y) →
      (∀ g j b, ‖w g j b‖ =
        Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) fun _ => a g j b)) →
      ‖∏ g, ∑ j, ((fun _ : Unit => (1 : ℤ)) j : ℂ) * ∏ b, w g j b‖ ≤
        Real.exp (-((1 : ℕ) : ℝ) * (T.ph (I2.th (E := E) P.q P.R0) - p16 E r P.q P.m R 1)) := by
    intro r' hr' hJ' w' a'
    subst hr'
    exact GlobalTheory.T.norm_prod_sum_theta_le_exp_torus E T DF P R 1 1 h1R le_rfl _ hsec hl2' (Fin (2 * R ^ 4)) Unit
      (by simp) hJ' (fun _ => 1) w' a' (fun _ => by simp)
  have hJ : Fintype.card Unit ≤ R ^ (2 * I2.PT.f E * r ^ 2) := by
    rw [Fintype.card_unit]; exact Nat.one_le_pow _ _ hR.pos
  have := key r hr hJ (fun g j b => Formalism.L2.PjFree.toC (w (xs b))) (fun g j b => ψ (z (xs b)))
    (fun g j b => hmem _) hgen' (fun g j b => hwn _)
  have e : ‖Formalism.L2.PjFree.toC (∏ b, w (xs b))‖ = ∏ b, ‖Formalism.L2.PjFree.toC (w (xs b))‖ := by
    rw [← norm_prod]; rfl
  rw [e]
  simpa [Finset.prod_const, norm_pow] using this

end GlobalTheory.ThetaConst.ArchBound

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ThetaConst

theorem normSq_thetaConst_le_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ), GoodEmb c σ → IsUnf U → ∀ R : ℕ, Odd R → 1 < R → ∀ (xs : Fin (Dw.p + Dw.q) → GlobalTheory.EtaForm.LatMod Dw (R ^ 4)) (f : Rul Xo c), Submodule.span (𝓞 E) (Set.range xs) = ⊤ → GlobalTheory.ThetaConst.IsTauRule Xo c R (fun _ : Unit => 1) (fun _ => xs) f → ∀ (DF q m : ℕ) (R0 : ℝ), GlobalTheory.EtaAn.RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ z : Σ k, Frame (U.X k).Ψ r, z.2 ∈ (U.X z.1).dom → homN U x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) z ≤ Real.exp ((GlobalTheory.EtaAn.p16 E r q m R 1 - ReciprocityTheory.ChartRestriction.G.I2.phiFD (U.X z.1) (ReciprocityTheory.ChartRestriction.G.I2.th (E := E) q R0) z.2) / (R : ℝ) ^ 4) := by
  intro E _ _ _ H Dw l Xo c σ r U x hσ hU R hR h1R xs f hsp hf DF q m R0 hrun hm z hz
  obtain ⟨k, y⟩ := z
  have hr := hU.1
  subst hr
  have hA : AllTest Xo c :=
    GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  have hsec1 : f ∈ sec Xo c 0 (Dw.p + Dw.q) := hf.mem_sec hR
  have hsec : f ^ 2 ∈ sec Xo c 0 (2 * (Dw.p + Dw.q)) := by
    have := sec_mul Xo c 0 0 _ _ hsec1 hsec1
    rw [add_zero, ← two_mul] at this
    rwa [sq]
  have hS : (U.X k).IsSec (laU U 0 (2 * (Dw.p + Dw.q)) k) (rdU U (f ^ 2) k) :=
    hU.2.2.2.2.1 0 _ ⟨fun _ => antitone_const, even_two_mul _⟩ (f ^ 2) hsec k
  obtain ⟨b, -, hb, hun, -, hphi, hp⟩ := _root_.GlobalTheory.EtaAn.exists_unit_frame E _ (U.X k) y hz
  have hN : homN U x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) ⟨k, y⟩ = ‖rdU U f k (rmul y b)‖ ^ 2 := by
    have h1 : lieFacZ Dw x (wtZ 0 (2 * (Dw.p + Dw.q))) = 1 := by simp [lieFacZ, wtZ]
    unfold homN ptN
    rw [modelWt_wtZ, h1, _root_.one_mul]
    show (U.X k).pnorm (laU U 0 (2 * (Dw.p + Dw.q)) k) (rdU U (f ^ 2) k) y = _
    rw [hp _ _ hS, sq f, GlobalTheory.AllWt.rdU_mul, Pi.mul_apply, Pi.mul_apply, norm_mul, sq]
  rw [hN, ← hphi _]
  have hv : rdU U f k (rmul y b) =
      Formalism.L2.PjFree.toC (evR Xo c f ((Formalism.L2.PjFree.Unf.ofPj U).un k ⟨rmul y b, hb⟩)) := dif_pos hb
  have key := ArchBound.norm_pow_le_at_unit_frame E H Dw l Xo c σ _ (Formalism.L2.PjFree.Unf.ofPj U) hσ
    ((Formalism.L2.PjFree.isUnf_ofPj U).2 hU) hA R hR h1R xs f hsp hf DF q m R0 hrun hm k ⟨rmul y b, hb⟩ hun
  rw [hv]
  have hn : R ^ 4 ≠ 0 := pow_ne_zero _ hR.pos.ne'
  have hR4 : (R : ℝ) ^ 4 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hR.pos.ne')
  rw [← pow_le_pow_iff_left₀ (sq_nonneg _) (Real.exp_pos _).le hn, ← pow_mul, ← Real.exp_nat_mul]
  refine le_of_le_of_eq key ?_
  congr 1
  push_cast
  rw [mul_div_cancel₀ _ hR4]
  show -((1 : ℝ)) * (I2.phiFD (U.X k) (I2.th (E := E) q R0) (rmul y b) - p16 E (Dw.p + Dw.q) q m R 1) = _
  ring

end GlobalTheory.ThetaConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB

namespace GlobalTheory.CovTest

def GdegPull : Prop :=
  ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ),
    IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X →
    π.residueDegree (genericPoint Y) ≠ 0 → ∀ L : HermLB p,
      gdeg (L.pull π hπ) D = (π.residueDegree (genericPoint Y) : ℝ) * gdeg L D

end GlobalTheory.CovTest

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelBijectiveOfPowEqZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup

theorem omegaLevel_bijective_of_pow_eq_zero : ∀ (p : ℕ)  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (G : PDivGroup p R) (n : ℕ), N ≤ n → Function.Bijective (G.omegaLevel n) := by
  intro p R _ N hN G n hn
  refine ⟨fun w w' h => ?_, G.omegaLevel_surjective n⟩
  rw [← sub_eq_zero]
  have h0 : (w - w').1 n = 0 := by
    simp only [omegaLevel_apply] at h
    change w.1 n - w'.1 n = 0
    rw [h, sub_self]
  obtain ⟨v, hv⟩ := (G.omega_val_eq_zero_iff n (w - w')).1 h0
  rw [hv, ← Nat.add_sub_cancel' hn, pow_add, hN, zero_mul, zero_smul]

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParCocIsCoc
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem parCoc_isCoc : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) (K : Type) (W : K → (A ⊗ B).left.Opens) (J : Type) [Fintype J] (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)), (∀ i, IsCoc (whole A) (a i)) → (∀ i, IsCoc (whole B) (b i)) → IsCupCob W a b n → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsCoc (parCov W x) (parCoc a b n x) := by
  intro R _ A B K W J _ a b n ha hb hn D _ _ x
  unfold IsCoc at ha hb ⊢
  unfold IsCupCob at hn
  intro E _ _ E' _ _ E'' _ _ φ ψ z hz
  have hz' : Sm W (z ≫ x ▷ B) := by
    unfold Sm at hz ⊢
    obtain ⟨k, hk⟩ := hz
    refine ⟨k, ?_⟩
    simpa [parCov, Over.comp_left, Scheme.Hom.comp_preimage] using hk
  have h1 := hn E E' E'' φ ψ (z ≫ x ▷ B) hz'
  have hfst : (z ≫ x ▷ B) ≫ fst _ _ = spOver (ptAlg (z ≫ fst _ _)) ≫ x := by
    rw [Category.assoc, whiskerRight_fst, ← Category.assoc, spOver_ptAlg]
  have hα : ptAlg ((spOver φ ≫ z) ≫ fst _ _) = φ.comp (ptAlg (z ≫ fst _ _)) := by
    rw [Category.assoc, ptAlg_comp]
  have ha' := fun i ↦ ha i D E E' (ptAlg (z ≫ fst _ _)) φ x (sm_whole _)
  have hb' := fun i ↦ hb i E E' E'' φ ψ (z ≫ snd _ _) (sm_whole _)
  rw [hfst] at h1
  simp only [Category.assoc, whiskerRight_snd] at h1
  simp only [parCoc]
  rw [hα]
  simp only [ha', hb', Category.assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_mul, map_add (f := _), AlgHom.comp_apply, add_mul, mul_add, Finset.sum_add_distrib]
  linear_combination -h1

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParCocSpOver
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem parCoc_spOver (R : Type) [CommRing R] (A B : Over (Sp R)) (J : Type) [Fintype J]
    (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) (ha : ∀ i, IsCoc (whole A) (a i))
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) :
    parCoc (D := D') a b n (spOver φ ≫ x) =
      ((parCoc (D := D) a b n x).pull (spOver φ ▷ B)).add
        (sumMul (D := D') (fun i ↦ a i D D' φ x) b) := by
  funext E _ _ E' _ _ ψ z
  simp only [parCoc, Fn1.pull, Fn1.add, sumMul]
  have h1 : z ≫ (spOver φ ≫ x) ▷ B = (z ≫ spOver φ ▷ B) ≫ x ▷ B := by
    rw [comp_whiskerRight, Category.assoc]
  have h2 : (z ≫ spOver φ ▷ B) ≫ snd _ _ = z ≫ snd _ _ := by
    rw [Category.assoc, whiskerRight_snd]
  have h3 : ptAlg ((z ≫ spOver φ ▷ B) ≫ fst _ _) =
      (ptAlg (z ≫ fst (SpAlg R D') B)).comp φ := by
    rw [Category.assoc, whiskerRight_fst, ← Category.assoc]
    conv_lhs => rw [← spOver_ptAlg (z ≫ fst (SpAlg R D') B)]
    rw [spOver_comp, ptAlg_spOver]
  rw [h1, h2, h3]
  have hc : ∀ i, a i D E ((ptAlg (z ≫ fst _ _)).comp φ) x =
      ptAlg (z ≫ fst _ _) (a i D D' φ x) + a i D' E (ptAlg (z ≫ fst _ _)) (spOver φ ≫ x) :=
    fun i ↦ ha i D D' E φ _ x (sm_whole x)
  simp only [hc, map_add (f := _), add_mul, Finset.sum_add_distrib]
  ring

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiScalarNsmulEqUnitMulPowSqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiScalar_nsmul_eq_unit_mul_pow_sq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D ga a → D.PsiEven → D.TauBimult → ∀ (χ : D.X) (n : ℕ), ∃ u : Rˣ, ((a (n • χ) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) (u : R) * ((a χ : (FractionRing R)ˣ) : FractionRing R) ^ (n ^ 2) := by
  first | exact @GlobalTheory.Mum.psiScal_nsmul_eq_unit_mul_pow | exact GlobalTheory.Mum.psiScal_nsmul_eq_unit_mul_pow | (intros; apply GlobalTheory.Mum.psiScal_nsmul_eq_unit_mul_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationDifferenceTrivialBaseChangeIffOverAStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translationDifference_trivial_baseChange_iff_over_A : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) (L : LB A.left), L.IsLB → ∀ (N : LB (A ⊗ T).left), N.IsLB → ∀ (Y : Over (Sp V)) (x : Y ⟶ GlobalTheory.TwistFlat.bc A φ) (U : Y.left.Opens), Triv ((LB.div (translDiff (GlobalTheory.TwistFlat.bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x) ((GlobalTheory.TwistFlat.twist A φ N).pull (snd Y (GlobalTheory.TwistFlat.bc A φ)).left)).pull ((fst Y (GlobalTheory.TwistFlat.bc A φ)).left ⁻¹ᵁ U).ι) ↔ Triv ((LB.div (translDiff A L (GlobalTheory.TwistFlat.upa φ x)) (ev N (snd (GlobalTheory.TwistFlat.up φ Y) A) (fst (GlobalTheory.TwistFlat.up φ Y) A ≫ GlobalTheory.TwistFlat.upt φ Y))).pull ((fst (GlobalTheory.TwistFlat.up φ Y) A).left ⁻¹ᵁ U).ι) := by
  first | exact @GlobalTheory.TwistFlat.triv_twist_iff | exact GlobalTheory.TwistFlat.triv_twist_iff | (intros; apply GlobalTheory.TwistFlat.triv_twist_iff <;> assumption)
end

