module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FirstCountableBlockMatrices
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0010
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0011
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0008

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BasisM
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.BasisPf

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

theorem basis_of (hI : Iwa) (hD : CayleyBlocksInvertible) (hM : Mult) (hC : CycSec) (hH : HolParam) : Basis := by
  intro m n ε c t p q e sL ρ hL _ _ W hW hWρ ν κ hν hκ ha hb P hP
  have := hν
  have := hW
  let sK := secK sL hL.cont
  let V : Submodule ℂ C(KR n, ℂ) := W.map sK
  let κC : C(KR n, ℂ) := ⟨κ, hκ⟩
  have hF0c := continuous_weight_factor (n := n) hD p q e

  have hflat : ∀ y : GR n, ∃ Q ∈ W, ∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * y) ∂ν = sL Q y' := by
    intro y
    obtain ⟨Q, hQW, hQ⟩ := hb 0 (fun g => F0 p q e (g * y)) (hF0c.comp (continuous_id.mul continuous_const))
      (fun y0 g hy0 => by
        simp only [Complex.cpow_zero, one_mul]
        rw [mul_assoc, ((hM n p q e).2 y0 (g * y) hy0).1])
    exact ⟨Q, hQW, fun y' => by simpa using hQ y'⟩
  choose QF hQFW hQF using hflat
  let v : GR n → V := fun y => ⟨sK (QF y), Submodule.mem_map_of_mem (hQFW y)⟩
  have hpi_v : ∀ y (h : C(KR n, ℂ)), (∀ k, h k = F0 p q e ((k : GR n) * y)) → piL ν κC h = sK (QF y) := by
    intro y h hh
    ext k'
    rw [piL_apply, secK_apply, ← hQF y (k' : GR n)]
    congr 1; funext k
    rw [hh]; simp [κC, mul_assoc]
  have hpi_W : ∀ Q ∈ W, piL ν κC (sK Q) = sK Q := by
    intro Q hQ
    ext k'
    rw [piL_apply, secK_apply, ← ha Q hQ (k' : GR n)]
    rfl

  have hspan : Submodule.span ℂ (range v) = ⊤ := by
    by_contra hne
    have hlt : Submodule.span ℂ (range v) < ⊤ := lt_top_iff_ne_top.2 hne
    obtain ⟨ℓ, hℓ0, hℓS⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    obtain ⟨pr, hpr⟩ := Submodule.ClosedComplemented.of_finiteDimensional V
    let ℓc : V →L[ℂ] ℂ := LinearMap.toContinuousLinearMap ℓ
    let L : C(KR n, ℂ) →L[ℂ] ℂ := ℓc.comp (pr.comp (piL ν κC))
    have hLv : ∀ (y : GR n) (h : C(KR n, ℂ)), (∀ k, h k = F0 p q e ((k : GR n) * y)) → L h = 0 := by
      intro y h hh
      have e1 : L h = ℓ (pr (piL ν κC h)) := rfl
      rw [e1, hpi_v y h hh]
      have e2 : pr (sK (QF y)) = v y := hpr (v y)
      rw [e2]
      have hmem : v y ∈ Submodule.span ℂ (range v) := Submodule.subset_span ⟨y, rfl⟩
      have : ℓ (v y) ∈ (Submodule.span ℂ (range v)).map ℓ := Submodule.mem_map_of_mem hmem
      rw [hℓS] at this
      simpa using this
    apply hℓ0
    ext ⟨x, hx⟩
    obtain ⟨Q, hQ, rfl⟩ := hx
    have h0 := hC m n ε c t p q e sL ρ hL L hLv Q (sK Q) (fun k => rfl)
    have e1 : L (sK Q) = ℓ (pr (piL ν κC (sK Q))) := rfl
    rw [e1, hpi_W Q hQ] at h0
    have e2 : pr (sK Q) = ⟨sK Q, Submodule.mem_map_of_mem hQ⟩ := hpr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩
    rw [e2] at h0
    simpa using h0

  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent ℂ (range v)
  have hs_top : ⊤ ≤ Submodule.span ℂ (range ((↑) : s → V)) := by
    rw [Subtype.range_coe, hs_span, hspan]
  let bV := Module.Basis.mk hs_li hs_top
  have : Finite s := Module.Finite.finite_basis bV
  have : Fintype s := Fintype.ofFinite s
  let N := Fintype.card s
  let b : Module.Basis (Fin N) ℂ V := bV.reindex (Fintype.equivFin s)
  have hbv : ∀ i, ∃ y, v y = b i := by
    intro i
    have hb' : (b i : V) = ((Fintype.equivFin s).symm i : V) := by
      simp [b, bV]
    rw [hb']
    exact hs_sub ((Fintype.equivFin s).symm i).2
  choose yy hyy using hbv
  let QQ : Fin N → PX m n := fun i => QF (yy i)
  have hQQ : ∀ i (k : KR n), ((b i : V) : C(KR n, ℂ)) k = sL (QQ i) (k : GR n) := by
    intro i k; rw [← hyy i]; rfl
  have hcoord : ∀ Q (hQ : Q ∈ W) (k : KR n), sL Q (k : GR n) =
      ∑ j, b.repr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩ j * sL (QQ j) (k : GR n) := by
    intro Q hQ k
    have h := congrArg (fun x : V => ((x : C(KR n, ℂ)) k)) (b.sum_repr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hQQ] at h
    rw [h]; rfl
  have hsum_sL : ∀ (d : Fin N → ℂ) (y : GR n), sL (∑ j, d j • QQ j) y = ∑ j, d j * sL (QQ j) y := by
    intro d y
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, Finset.sum_apply]
  let cc : Fin N → ℂ := fun j => b.repr ⟨sK P, Submodule.mem_map_of_mem hP⟩ j
  have hPsum : ∀ y, sL P y = ∑ j, cc j * sL (QQ j) y := by
    intro y
    rw [flatEq_of hI m n ε c t p q e sL ρ hL P (∑ j, cc j • QQ j) (fun k hk => by
      rw [hcoord P hP ⟨k, hk⟩, hsum_sL]) y, hsum_sL]

  let f : Fin N → KR n → ℂ := fun j k => sL (QQ j) (k : GR n)
  have hfli : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h2 : ∑ j, g j • b j = 0 := by
      apply Subtype.ext
      ext k
      have := congrFun hg k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, f] at this
      simp only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hQQ, Submodule.coe_zero, ContinuousMap.zero_apply]
      exact this
    exact Fintype.linearIndependent_iff.1 b.linearIndependent g h2
  obtain ⟨kk, hkk⟩ := exists_pts N f hfli
  let A : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun j l => f j (kk l)
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 hkk
  let Ev : ℂ → Matrix (Fin N) (Fin N) ℂ := fun w => Matrix.of fun i l =>
    ∫ k, κ k * ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e ((kk l : GR n) * (k : GR n) * yy i)) ∂ν
  let M : ℂ → Matrix (Fin N) (Fin N) ℂ := fun w => Ev w * A⁻¹
  have hEv0 : Ev 0 = A := by
    ext i l
    simp only [Ev, A, f, Matrix.of_apply, Complex.cpow_zero, one_mul]
    exact hQF (yy i) (kk l)
  have hM0 : M 0 = 1 := by
    show Ev 0 * A⁻¹ = 1
    rw [hEv0]; exact Matrix.mul_nonsing_inv A hA
  have hEvd : ∀ i l, Differentiable ℂ (fun w => Ev w i l) := by
    intro i l
    have hcg : Continuous (fun k : KR n => (kk l : GR n) * (k : GR n) * yy i) :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    have hpos : ∀ k : KR n, 0 < hLoc ((kk l : GR n) * (k : GR n) * yy i) := fun k => hLoc_pos hD _
    have h := (hH (KR n) ν univ isCompact_univ (by simp) univ
      (fun k w => κ k * ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e ((kk l : GR n) * (k : GR n) * yy i)))
      isOpen_univ ?_ ?_).1
    · exact differentiableOn_univ.1 h
    · refine Continuous.continuousOn ?_
      refine (hκ.comp continuous_fst).mul (Continuous.mul ?_ (hF0c.comp (hcg.comp continuous_fst)))
      exact Continuous.cpow (Complex.continuous_ofReal.comp ((continuous_hLoc hD).comp (hcg.comp continuous_fst)))
        continuous_snd (fun y => Complex.ofReal_mem_slitPlane.2 (hpos y.1))
    · intro k _
      have hne : ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos k).ne'
      exact ((((differentiable_id.const_cpow (Or.inl hne)).mul_const _).const_mul _)).differentiableOn
  have hMd : ∀ i j, Differentiable ℂ (fun w => M w i j) := by
    intro i j
    show Differentiable ℂ (fun w => (Ev w * A⁻¹) i j)
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum fun l _ => (hEvd i l).mul_const _
  refine ⟨N, yy, QQ, cc, M, fun j => hQFW (yy j), hPsum, hM0, hMd, fun i y' => hQF (yy i) y', ?_⟩
  intro w i y'
  let fw : GR n → ℂ := fun g => (hLoc (g * yy i) : ℂ) ^ w * F0 p q e (g * yy i)
  have hfwc : Continuous fw := by
    have hg : Continuous (fun g : GR n => g * yy i) := continuous_id.mul continuous_const
    refine Continuous.mul ?_ (hF0c.comp hg)
    exact Continuous.cpow (Complex.continuous_ofReal.comp ((continuous_hLoc hD).comp hg)) continuous_const
      (fun g => Complex.ofReal_mem_slitPlane.2 (hLoc_pos hD _))
  have hfwlaw : ∀ (y0 g : GR n), (mR y0).toBlocks₂₁ = 0 → fw (y0 * g) = (hLoc y0 : ℂ) ^ w * F0 p q e y0 * fw g := by
    intro y0 g hy0
    simp only [fw]
    rw [mul_assoc y0 g (yy i)]
    obtain ⟨h1, h2⟩ := (hM n p q e).2 y0 (g * yy i) hy0
    rw [h1, h2]
    push_cast
    rw [Complex.mul_cpow_ofReal_nonneg (hLoc_pos hD y0).le (hLoc_pos hD _).le]
    ring
  obtain ⟨Qw, hQwW, hQw⟩ := hb w fw hfwc hfwlaw
  let a := b.repr ⟨sK Qw, Submodule.mem_map_of_mem hQwW⟩
  have hEva : ∀ l, Ev w i l = ∑ j, a j * A j l := by
    intro l
    have h1 := hQw (kk l : GR n)
    rw [hLoc_K hM _ (kk l).2] at h1
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at h1
    rw [hcoord Qw hQwW (kk l)] at h1
    simp only [Ev, A, f, Matrix.of_apply]
    rw [← h1]
  have hrow : (fun l => Ev w i l) = Matrix.vecMul a A := by
    funext l; rw [hEva l]; simp [Matrix.vecMul, dotProduct]
  have hMa : ∀ j, M w i j = a j := by
    intro j
    have e1 : M w i j = Matrix.vecMul (fun l => Ev w i l) A⁻¹ j := by
      simp [M, Matrix.mul_apply, Matrix.vecMul, dotProduct]
    rw [e1, hrow, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hA, Matrix.vecMul_one]
  have hflatw : ∀ y, sL Qw y = ∑ j, M w i j * sL (QQ j) y := by
    intro y
    rw [flatEq_of hI m n ε c t p q e sL ρ hL Qw (∑ j, M w i j • QQ j) (fun k hk => by
      rw [hcoord Qw hQwW ⟨k, hk⟩, hsum_sL]
      simp only [hMa]; rfl) y, hsum_sL]
  rw [show (∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e (y' * (k : GR n) * yy i)) ∂ν) =
      ∫ k, κ k * fw (y' * (k : GR n)) ∂ν from rfl, hQw y', hflatw]

end PositivityTheory.Rg.Sw.AbsSt.BasisPf

namespace PositivityTheory.Rg.Sw.AbsSt

theorem basis (hI : Iwa) (hD : CayleyBlocksInvertible) (hM : Mult) (hC : CycSec) (hH : HolParam) : Basis :=
  BasisPf.basis_of hI hD hM hC hH

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightC
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def FarRightC : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)), GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I →
      ∃ σ : ℝ, (∀ Q g, DifferentiableOn ℂ (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z Q) g) (GlobalTheory.Cont.rightOf σ)) ∧
        (∀ Q g (z : ℂ), σ < z.re → Summable fun q => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q) ∧
        ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (ν : Measure (KR n)) (κ : KR n → ℂ) (N : ℕ) (yy : Fin N → GR n)
          (QQ : Fin N → PX m n) (M : ℂ → Matrix (Fin N) (Fin N) ℂ), IsFiniteMeasure ν → Continuous κ →
          (∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
              F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y') →
          ∀ (z : ℂ), σ < z.re → ∀ (g : G) (i : Fin N),
            ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
              ∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g

def TSGenC : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)), GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I →
      ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (W : Submodule ℂ (PX m n)), FiniteDimensional ℂ W →
        (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) → ∀ (ν : Measure (KR n)) (κ : KR n → ℂ), IsFiniteMeasure ν →
        Continuous κ → (∀ Q ∈ W, ∀ y : GR n, ∫ k, κ k * sL Q (y * (k : GR n)) ∂ν = sL Q y) →
        (∀ (w : ℂ) (f : GR n → ℂ), Continuous f →
          (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → f (y * g) = (hLoc y : ℂ) ^ w * F0 p q e y * f g) →
          ∃ Q ∈ W, ∀ y : GR n, ∫ k, κ k * f (y * (k : GR n)) ∂ν = (hLoc y : ℂ) ^ w * sL Q y) →
        ∀ (g : G) (y : GR n) (Q : PX m n), Q ∈ W → (∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * y) ∂ν = sL Q y') →
          ∫ k, κ k * I 1 (g * ι ((k : GR n) * y)) ∂ν = I Q g

def VacData {n : ℕ} {m : ℕ} {G : Type} [Group G] [TopologicalSpace G] (Pp Γ : Subgroup G) (s₀ : ℂ) (Ht : G → ℝ≥0)
    (sec I : PX m n →ₗ[ℂ] (G → ℂ)) : Prop :=
  ∃ (r : ℝ) (F : ℂ → G → ℂ), 0 < r ∧ ContinuousOn (fun y : ℂ × G => F y.1 y.2) (Metric.ball s₀ r ×ˢ univ) ∧
    (∀ g, DifferentiableOn ℂ (F · g) (Metric.ball s₀ r)) ∧ (∀ g, F s₀ g = I 1 g) ∧
    ∀ g, ∀ z ∈ Metric.ball s₀ r, GlobalTheory.Cont.HolValueAt
      (fun w => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (w - s₀) * sec 1 x) g) z (F z g)

def GenCore : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)), GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I → VacData Pp Γ s₀ Ht sec I →
      ∀ P g, GlobalTheory.Cont.HolValueAt
        (fun z => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec P x) g) s₀ (I P g)

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HasDerivAtPhi
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem norm_scal_sq (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) (s : ℝ) (a : Fin m) (j : Fin n) :
    ‖scal (aH X s) y a j‖ ^ 2 = Real.exp (s * X j) ^ 2 * ‖y a j‖ ^ 2 := by
  simp only [scal, aH, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]

theorem hasDerivAt_gs (c : ℝ) (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) (h : ℝ) :
    HasDerivAt (fun s => gs c (scal (aH X s) y))
      (gs c (scal (aH X h) y) * (-(((c * ∑ a, ∑ j, 2 * X j * ‖scal (aH X h) y a j‖ ^ 2) : ℝ) : ℂ))) h := by
  have key : ∀ s : ℝ, gs c (scal (aH X s) y) =
      Complex.exp (-(((c * ∑ a, ∑ j, Real.exp (s * X j) ^ 2 * ‖y a j‖ ^ 2 : ℝ)) : ℂ)) := by
    intro s
    simp only [gs, norm_scal_sq]
  have hF : HasDerivAt (fun s : ℝ => c * ∑ a, ∑ j, Real.exp (s * X j) ^ 2 * ‖y a j‖ ^ 2)
      (c * ∑ a, ∑ j, 2 * X j * (Real.exp (h * X j) ^ 2 * ‖y a j‖ ^ 2)) h := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro a _
    apply HasDerivAt.fun_sum
    intro j _
    have e : HasDerivAt (fun s : ℝ => Real.exp (s * X j)) (Real.exp (h * X j) * X j) h := by
      simpa using ((hasDerivAt_id h).mul_const (X j)).exp
    exact ((e.pow 2).mul_const (‖y a j‖ ^ 2)).congr_deriv (by
      rw [show (2 : ℕ) - 1 = 1 from rfl]
      push_cast
      ring)
  have hc := (hF.ofReal_comp.neg).cexp
  rw [show (fun s : ℝ => gs c (scal (aH X s) y)) = fun s : ℝ =>
      Complex.exp (-(((c * ∑ a, ∑ j, Real.exp (s * X j) ^ 2 * ‖y a j‖ ^ 2 : ℝ)) : ℂ)) from funext key]
  refine hc.congr_deriv ?_
  rw [key h]
  simp only [norm_scal_sq, Pi.neg_apply]

theorem hasDerivAt_phi (c : ℝ) (X : Fin n → ℝ) (Q : PX m n) (y : Fin m → Fin n → ℂ) (h : ℝ) :
    HasDerivAt (fun s => evX Q (scal (aH X s) y) * gs c (scal (aH X s) y))
      ((evX (dil c X Q) (scal (aH X h) y) - ((m : ℂ) * ∑ j, (X j : ℂ)) * evX Q (scal (aH X h) y)) *
        gs c (scal (aH X h) y)) h := by
  have h1 : HasDerivAt (fun s : ℝ => evX Q (scal (aH X s) y))
      (∑ k, eval (ept (scal (aH X h) y)) (pderiv k Q) * ((X k.2.1 : ℂ) * ept (scal (aH X h) y) k)) h := by
    simp only [evX_eq]
    exact hasDerivAt_eval_curve Q (fun s => ept (scal (aH X s) y)) _ h
      (fun k => hasDerivAt_scal_coord X y h k)
  exact (h1.mul (hasDerivAt_gs c X y h)).congr_deriv (by
    rw [evX_dil]
    push_cast
    ring)

private theorem dom_bound_lemma (X : Fin n → ℝ) (h : ℝ) (hh : |h| < 1) (j : Fin n) :
    Real.exp (-(∑ i, |X i|)) ≤ Real.exp (h * X j) ∧ Real.exp (h * X j) ≤ Real.exp (∑ i, |X i|) := by
  have hj : |X j| ≤ ∑ i, |X i| :=
    Finset.single_le_sum (f := fun i => |X i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  have hx : |h * X j| ≤ ∑ i, |X i| := by
    rw [abs_mul]
    calc |h| * |X j| ≤ 1 * |X j| := mul_le_mul_of_nonneg_right hh.le (abs_nonneg _)
      _ ≤ ∑ i, |X i| := by simpa using hj
  constructor
  · exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (h * X j)])
  · exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) hx)

private theorem dom_bound_lemma_2 (X : Fin n → ℝ) (h : ℝ) (hh : |h| < 1) (y : Fin m → Fin n → ℂ) :
    ‖scal (aH X h) y‖ ≤ Real.exp (∑ i, |X i|) * ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  have e := (dom_bound_lemma X h hh j).2
  have hy : ‖y a j‖ ≤ ‖y‖ := (norm_le_pi_norm (y a) j).trans (norm_le_pi_norm y a)
  have hn : ‖scal (aH X h) y a j‖ = Real.exp (h * X j) * ‖y a j‖ := by
    simp only [scal, aH, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hn]
  exact mul_le_mul e hy (norm_nonneg _) (Real.exp_pos _).le

private theorem dom_bound_lemma_3 (X : Fin n → ℝ) (h : ℝ) (hh : |h| < 1) (y : Fin m → Fin n → ℂ) :
    Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2 ≤ ∑ a, ∑ j, ‖scal (aH X h) y a j‖ ^ 2 := by
  calc Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2
        ≤ Real.exp (-(∑ i, |X i|)) ^ 2 * ∑ a, ∑ j, ‖y a j‖ ^ 2 := by
          gcongr
          exact sq_norm_le_sum y
    _ = ∑ a, ∑ j, Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y a j‖ ^ 2 := by
          simp only [Finset.mul_sum]
    _ ≤ ∑ a, ∑ j, ‖scal (aH X h) y a j‖ ^ 2 := by
          gcongr with a _ j _
          rw [norm_scal_sq]
          gcongr
          exact Real.exp_le_exp.mp (dom_bound_lemma X h hh j).1

theorem dom_bound (c : ℝ) (hc : 0 < c) (X : Fin n → ℝ) (P : PX m n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, |h| < 1 → ∀ y : Fin m → Fin n → ℂ,
      ‖evX P (scal (aH X h) y) * gs c (scal (aH X h) y)‖ ≤
        K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by
  obtain ⟨C, k, hC, hP⟩ := poly_bound P
  have hM0 : 0 ≤ ∑ i, |X i| := Finset.sum_nonneg fun i _ => abs_nonneg (X i)
  have hκ : 0 < c * Real.exp (-(∑ i, |X i|)) ^ 2 := by positivity
  obtain ⟨D, hD, hdec⟩ := decay k _ hκ ((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)
  refine ⟨C * Real.exp (∑ i, |X i|) ^ k * D, by positivity, fun h hh y => ?_⟩
  have hv := dom_bound_lemma_2 X h hh y
  have hs := dom_bound_lemma_3 X h hh y
  have hg : ‖gs c (scal (aH X h) y)‖ ≤
      Real.exp (-(c * Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2)) := by
    rw [gs, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hs hc.le]
  have hp : ‖evX P (scal (aH X h) y)‖ ≤ C * Real.exp (∑ i, |X i|) ^ k * (1 + ‖y‖) ^ k := by
    calc ‖evX P (scal (aH X h) y)‖ ≤ C * (1 + ‖scal (aH X h) y‖) ^ k := hP _
      _ ≤ C * (Real.exp (∑ i, |X i|) * (1 + ‖y‖)) ^ k := by
          gcongr
          have : 1 ≤ Real.exp (∑ i, |X i|) := Real.one_le_exp hM0
          nlinarith [norm_nonneg y]
      _ = C * Real.exp (∑ i, |X i|) ^ k * (1 + ‖y‖) ^ k := by
          rw [mul_pow, mul_assoc]
  calc ‖evX P (scal (aH X h) y) * gs c (scal (aH X h) y)‖
        = ‖evX P (scal (aH X h) y)‖ * ‖gs c (scal (aH X h) y)‖ := norm_mul _ _
    _ ≤ (C * Real.exp (∑ i, |X i|) ^ k * (1 + ‖y‖) ^ k) *
          Real.exp (-(c * Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2)) := by
          gcongr
    _ = C * Real.exp (∑ i, |X i|) ^ k *
          ((1 + ‖y‖) ^ k * Real.exp (-(c * Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2))) := by ring
    _ ≤ C * Real.exp (∑ i, |X i|) ^ k *
          (D * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (hdec _ (norm_nonneg y)) (by positivity)
    _ = C * Real.exp (∑ i, |X i|) ^ k * D *
          (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by ring

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LamCont
section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] {ε : Fin m → Bool} {c t : ℝ}
  {sL : PX m n →ₗ[ℂ] (GR n → ℂ)} {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ}
  {Ht : G → ℝ≥0} {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem lam_cont (hBH : BanachHol) (hFL : FactorL) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) {B : Set ℂ} (hB : IsOpen B) {w : ℂ} (hw : w ∈ B) (F : ℂ → G → ℂ)
    (hFc : ContinuousOn (fun y : ℂ × G => F y.1 y.2) (B ×ˢ univ)) (hFh : ∀ g, DifferentiableOn ℂ (F · g) B)
    (hFi : ∀ z ∈ B, ∀ γ ∈ Γ, ∀ g, F z (γ * g) = F z g) : ContinuousAt (fun z => l (F z)) w := by
  obtain ⟨C, hCc, hCb⟩ := hG.Λbd l hl
  obtain ⟨L, hL⟩ := hFL G (invSub Γ) l C hCc (fun F hF => hF.1)
    (fun a F hF F' hF' => hG.Λadd l hl a F F' hF.1 hF'.1 hF.2 hF'.2)
    (fun F hF M hM => hCb F M hF.1 hF.2 hM)
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  have hFcont : ∀ z ∈ B, Continuous (F z) := by
    intro z hzB
    exact hFc.comp_continuous (continuous_const.prodMk continuous_id) (fun g => ⟨hzB, mem_univ g⟩)
  obtain ⟨Φ, hΦd, hΦ⟩ := hBH C B (fun z x => F z x) hB
    (hFc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun y hy => ⟨hy.1, mem_univ _⟩))
    (fun x => hFh x)
  have hfeq : ∀ z ∈ B, l (F z) = L (Φ z) := by
    intro z hzB
    have hmem : F z ∈ invSub Γ := ⟨hFcont z hzB, hFi z hzB⟩
    rw [hL (F z) hmem (hFcont z hzB)]
    congr 1
    ext x
    rw [hΦ z hzB x]
    rfl
  have hd : DifferentiableOn ℂ (fun z => l (F z)) B :=
    (L.differentiable.comp_differentiableOn hΦd).congr hfeq
  exact (hd.differentiableAt (hB.mem_nhds hw)).continuousAt

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphOf
section
namespace PositivityTheory.Rg.Sw.AbsSt

theorem thSph_of : KAK → Mult → DerivativeVacuumDilations → Sph → SecZero → HolParam → LC → NullIff → ThSph :=
  fun hKAK hMult hD hSph hSZ hHP hLC _ => thSph_of' helpA helpC hKAK hMult hD hSph hSZ hHP hLC

end PositivityTheory.Rg.Sw.AbsSt
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TsGen
section
namespace PositivityTheory.Rg.Sw.AbsSt

theorem tsGen : Iwa → CayleyBlocksInvertible → KAK → Mult → SecZero → DerivativeVacuumDilations → HolParam → LC → TSGen :=
  fun _ hD hK hM hS hDF hH hLC => tsGen_of hD hK hM hS hDF hH hLC tsbFacts

end PositivityTheory.Rg.Sw.AbsSt
end

