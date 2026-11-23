module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0558
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctional
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0370
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0358
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0377

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModerateGrowthConvolutionIntegral
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

noncomputable section

namespace GlobalTheory.CompanionTheory.GrowthConv

open GlobalTheory.CompanionTheory.ArchSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def rmulLin : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) where
  toFun := rmul
  map_add' x y := ContinuousLinearMap.ext fun z =>
    mul_add (Matrix.of z) (Matrix.of x) (Matrix.of y)
  map_smul' c x := ContinuousLinearMap.ext fun z =>
    Matrix.mul_smul (Matrix.of z) c (Matrix.of x)

def lmulLin : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) where
  toFun := lmul
  map_add' x y := ContinuousLinearMap.ext fun z =>
    add_mul (Matrix.of x) (Matrix.of y) (Matrix.of z)
  map_smul' c x := ContinuousLinearMap.ext fun z =>
    Matrix.smul_mul c (Matrix.of x) (Matrix.of z)

theorem continuous_rmul : Continuous (rmul : Lie E a → (Lie E a →L[ℝ] Lie E a)) :=
  (rmulLin (E := E) (a := a)).continuous_of_finiteDimensional

theorem continuous_lmul : Continuous (lmul : Lie E a → (Lie E a →L[ℝ] Lie E a)) :=
  (lmulLin (E := E) (a := a)).continuous_of_finiteDimensional

def bnd (c : GL (Fin a) (Cinf E)) : ℝ := 1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖

theorem height_mul_le_bnd (c y : GL (Fin a) (Cinf E)) : height (y * c) ≤ bnd c * height y := by
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height bnd
  rw [h1, h2]
  nlinarith

theorem toGL_inv (u : AutomorphicForm.archGroup E a) : toGL E a u⁻¹ = (toGL E a u)⁻¹ := by
  simp only [toGL, map_inv]

theorem continuous_bnd : Continuous fun u : AutomorphicForm.archGroup E a => bnd (toGL E a u) := by
  have hm : Continuous (mMap E a) := (mMap E a).continuous_of_finiteDimensional
  have hv : Continuous fun u : AutomorphicForm.archGroup E a =>
      ((u : (AutomorphicForm.ArchMatrix E a)ˣ) : AutomorphicForm.ArchMatrix E a) :=
    Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun u : AutomorphicForm.archGroup E a => toL (toGL E a u).val := by
    simp_rw [toL_toGL]
    exact hm.comp hv
  have h2 : Continuous fun u : AutomorphicForm.archGroup E a => toL ((toGL E a u)⁻¹).val := by
    simp_rw [← toGL_inv, toL_toGL]
    exact hm.comp (hv.comp continuous_inv)
  unfold bnd
  exact (continuous_const.add (continuous_rmul.comp h1).norm).add (continuous_lmul.comp h2).norm

theorem growth_conv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ ψ : GA E a → ℂ), Continuous φ → (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) → ∀ D : AutomorphicForm.archGroup E a → ℂ, Continuous D → HasCompactSupport D → (∀ g, ψ g = ∫ y, φ (g * AutomorphicForm.infEmb E a y) * D y ∂ν) → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ (g * infGL E a y)‖ ≤ C * height y ^ N := by
  intro E _ _ _ a _ _ ν _ φ ψ _ hgrow D hD hDc hψ g
  obtain ⟨C, N, hC⟩ := hgrow g
  have hpos : ∀ y : GL (Fin a) (Cinf E), 0 ≤ height y := fun y => by
    linarith [one_le_height y]
  have C0 : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left h1 hp
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (f := fun u : AutomorphicForm.archGroup E a => bnd (toGL E a u))
    hDc continuous_bnd.continuousOn
  have hint : Integrable (fun u => ‖D u‖) ν := (hD.integrable_of_hasCompactSupport hDc).norm
  refine ⟨C * B ^ N * ∫ u, ‖D u‖ ∂ν, N, fun y => ?_⟩
  have pt : ∀ u, ‖φ (g * infGL E a y * AutomorphicForm.infEmb E a u) * D u‖ ≤
      (C * (B * height y) ^ N) * ‖D u‖ := fun u => by
    by_cases hu : u ∈ tsupport D
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have e : g * infGL E a y * AutomorphicForm.infEmb E a u = g * infGL E a (y * toGL E a u) := by
        rw [infEmb_eq, mul_assoc, map_mul]
      rw [e]
      refine (hC _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos _) ?_ N) C0)
      exact (height_mul_le_bnd _ y).trans
        (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hB u hu)) (hpos y))
    · rw [image_eq_zero_of_notMem_tsupport hu]
      simp
  have key := norm_integral_le_of_norm_le (hint.const_mul (C * (B * height y) ^ N)) (Filter.Eventually.of_forall pt)
  rw [hψ]
  refine key.trans (le_of_eq ?_)
  rw [integral_const_mul, mul_pow]
  ring

end GlobalTheory.CompanionTheory.GrowthConv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusHalfBlockValue
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS

theorem ordL_pow_div_pow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x y : L}
    (hx : x ≠ 0) (hy : y ≠ 0) (a b : ℕ) :
    ordL (x ^ b / y ^ a) = (b : ℤ) * ordL x - (a : ℤ) * ordL y := by
  have h : x ^ b / y ^ a =
      (((Units.mk0 x hx) ^ (b : ℤ) * (Units.mk0 y hy) ^ (-(a : ℤ)) : Lˣ) : L) := by
    simp [div_eq_mul_inv]
  rw [h, Units.val_mul, GlobalTheory.CompanionTheory.SwapInt.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _),
    GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow, GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow]
  simp only [Units.val_mk0]
  ring

theorem absHalf_blockDet_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = (qV E w : ℂ) ^ (-((i : ℂ) * b - (j : ℂ) * a) / 2) := by
  intro E _ _ _ a b w i j m hi hj
  have h1 : m.1.val.det ≠ 0 := by
    have := m.1.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have h2 : m.2.val.det ≠ 0 := by
    have := m.2.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hq : 0 < (qV E w : ℝ) := by
    have : qV E w ≠ 0 := by
      unfold qV
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have ho := ordL_pow_div_pow h1 h2 a b
  rw [hi, hj] at ho
  unfold absHalf
  rw [ho]
  have hs : Real.sqrt ((qV E w : ℝ) ^ (-((b : ℤ) * (i : ℤ) - (a : ℤ) * (j : ℤ)))) =
      (qV E w : ℝ) ^ (-((i : ℝ) * b - (j : ℝ) * a) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq.le]
    congr 1
    push_cast
    ring
  rw [hs, Complex.ofReal_cpow hq.le, Complex.ofReal_natCast]
  congr 1
  push_cast
  ring

end GlobalTheory.CompanionTheory.CtS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealReadLevi
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.CompanionTheory.ReadLevel

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ g ∈ K, ρ g v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩

theorem extTensor_twRep {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (χ : G →* ℂˣ) (ψ : H →* ℂˣ)
    (m : G × H) (x : V ⊗[ℂ] W) :
    GlobalTheory.SmGL.extTensor (twRep ρ χ) (twRep σ ψ) m x =
      ((χ m.1 * ψ m.2 : ℂˣ) : ℂ) • GlobalTheory.SmGL.extTensor ρ σ m x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v u =>
    rw [GlobalTheory.SmGL.extTensor_tmul, GlobalTheory.SmGL.extTensor_tmul, twRep_apply, twRep_apply,
      TensorProduct.smul_tmul_smul, Units.val_mul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem isSpherical_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) {K : Subgroup G}
    (h : fixed σ K ≠ ⊥) : GlobalTheory.LGrp.IsSpherical ρ K := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine (Submodule.ne_bot_iff _).2 ⟨φ.toLinearEquiv.symm v, ?_, fun e => hv0 (by
    have h2 := congrArg φ.toLinearEquiv e
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2)⟩
  refine mem_fixed_iff.2 fun g hg => φ.toLinearEquiv.injective ?_
  have h1 : φ.toLinearEquiv (ρ g (φ.toLinearEquiv.symm v)) = σ g (φ.toLinearEquiv (φ.toLinearEquiv.symm v)) :=
    LinearMap.congr_fun (φ.isIntertwining' g) _
  rw [h1, LinearEquiv.apply_symm_apply]
  exact mem_fixed_iff.1 hv g hg

theorem fixed_ind₂_ne_bot (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b n : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin a) k × GL (Fin b) k) W) (K : Subgroup (GL (Fin n) k))
    (hK : IsOpen (K : Set (GL (Fin n) k))) (x : W) (hx : x ≠ 0)
    (hfix : ∀ p : GlobalTheory.SmGL.parab k (GlobalTheory.SmGL.two e), (p : GL (Fin n) k) ∈ K →
      ((GlobalTheory.SmGL.deltaHalf k (GlobalTheory.SmGL.Two (Fin a) (Fin b)) (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p) : ℂˣ) : ℂ) •
        ρ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)) x = x) :
    fixed (GlobalTheory.SmGL.ind₂ e ρ) K ≠ ⊥ :=
  _root_.GlobalTheory.CompanionTheory.SmInd.fixed_smInd_ne_bot_of_fixed _ _ _ _ K hK x hx hfix

theorem exists_fixed_of_sep {G V X : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G V} {S : Submodule ℂ V} {τ : Representation ℂ G X}
    (hs : Sep ρ S τ) {L : Subgroup G} (hL : IsOpen (L : Set G)) {v : V} (hv : v ∈ S) (hv0 : v ≠ 0)
    (hfix : v ∈ fixed ρ L) : ∃ x : X, x ≠ 0 ∧ ∀ m ∈ L, τ m x = x := by
  obtain ⟨-, J, Lj, hLj, hsep⟩ := hs
  have hsm : SmVec ρ v := ⟨L, hL, hfix⟩
  obtain ⟨j, hj⟩ : ∃ j, Lj j v ≠ 0 := by
    by_contra hc
    exact hv0 (hsep v hv hsm fun j => by_contra fun hj => hc ⟨j, hj⟩)
  refine ⟨Lj j v, hj, fun m hm => ?_⟩
  rw [← hLj j m v hv hsm, mem_fixed_iff.1 hfix m hm]

theorem fixed_ind₂_twist (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b n : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin a) k) V) (σ : Representation ℂ (GL (Fin b) k) W)
    (χ : GL (Fin a) k →* ℂˣ) (ψ : GL (Fin b) k →* ℂˣ)
    (K : Subgroup (GL (Fin n) k)) (hKo : IsOpen (K : Set (GL (Fin n) k))) (hKc : IsCompact (K : Set (GL (Fin n) k)))
    (x : V ⊗[ℂ] W) (hx : x ≠ 0)
    (hfix : ∀ p : GlobalTheory.SmGL.parab k (GlobalTheory.SmGL.two e), (p : GL (Fin n) k) ∈ K →
      GlobalTheory.SmGL.extTensor ρ σ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)) x = x ∧
      χ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).1 *
        ψ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).2 = 1) :
    fixed (GlobalTheory.SmGL.ind₂ e (GlobalTheory.SmGL.extTensor (twRep ρ χ) (twRep σ ψ))) K ≠ ⊥ := by
  refine fixed_ind₂_ne_bot k e _ K hKo x hx fun p hp => ?_
  obtain ⟨h1, h2⟩ := hfix p hp
  rw [_root_.GlobalTheory.CompanionTheory.ModCompactParab.deltaHalf_leviProj_eq_one_of_isCompact k a b n e K hKc p hp, Units.val_one, one_smul, extTensor_twRep, h1, h2, Units.val_one, one_smul]

theorem isSpherical_of_join (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b n : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) U)
    (ρ : Representation ℂ (GL (Fin a) k) V) (σ : Representation ℂ (GL (Fin b) k) W)
    (χ : GL (Fin a) k →* ℂˣ) (ψ : GL (Fin b) k →* ℂˣ)
    (φ : π.Equiv (GlobalTheory.SmGL.ind₂ e (GlobalTheory.SmGL.extTensor (twRep ρ χ) (twRep σ ψ))))
    (K : Subgroup (GL (Fin n) k)) (hKo : IsOpen (K : Set (GL (Fin n) k))) (hKc : IsCompact (K : Set (GL (Fin n) k)))
    (x : V ⊗[ℂ] W) (hx : x ≠ 0)
    (hfix : ∀ p : GlobalTheory.SmGL.parab k (GlobalTheory.SmGL.two e), (p : GL (Fin n) k) ∈ K →
      GlobalTheory.SmGL.extTensor ρ σ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)) x = x ∧
      χ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).1 *
        ψ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).2 = 1) :
    GlobalTheory.LGrp.IsSpherical π K :=
  isSpherical_of_equiv φ (fixed_ind₂_twist k e ρ σ χ ψ K hKo hKc x hx hfix)

theorem loc_pow {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (w : Pl E) (k : ℕ)
    (x : (w.adicCompletion E)ˣ) : (μ ^ k).loc w x = μ.loc w (x ^ k) := by
  rw [map_pow]
  induction k with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ k ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem twist_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (μ : HChar E) (w : Pl E)
    (m : GLw a w × GLw b w)
    (h : μ.loc w (GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) = 1) :
    (((μ ^ b).loc w).comp GeneralLinearGroup.det) m.1 * (((μ ^ a).loc w).comp GeneralLinearGroup.det) m.2 = 1 := by
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, loc_pow, loc_pow, ← map_mul, h]

theorem levi_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (K : Subgroup (GLw n w)) (Q : GLw a w × GLw b w → Prop) (hKQ : ∀ m X, blk h w m X ∈ K → Q m)
    (p : GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))) (hp : (p : GLw n w) ∈ K) :
    Q ((GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm
      (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) p)) := by
  obtain ⟨X, hX⟩ := _root_.GlobalTheory.CompanionTheory.ParabBlock.parab_eq_blk E n a b h w p
  exact hKQ _ X (hX ▸ hp)

set_option maxHeartbeats 1000000 in
theorem rReadLev : RReadLev := by
  intro hR hJ E _ _ _ n a b h μ s₁ s₂ Pa Pb D c w K L G hKo hKc hLo hKL hG hG0 hGL
  obtain ⟨x, hx0, hx⟩ := exists_fixed_of_sep (hR E a b s₁ s₂ Pa Pb w c.g₁ c.g₂ c.u₁ c.u₂ c.t₁ c.t₂) hLo hG hG0 hGL
  obtain ⟨φ⟩ := hJ E n a b h (μ ^ b) (μ ^ a) Pa Pb D w c.join
  exact isSpherical_of_join (w.adicCompletion E) (GlobalTheory.SmGL.stdSum h) (lp D w) (lp Pa w) (lp Pb w)
    (((μ ^ b).loc w).comp GeneralLinearGroup.det) (((μ ^ a).loc w).comp GeneralLinearGroup.det)
    φ K hKo hKc x hx0 fun p hp =>
      have hq := levi_of_mem h w K _ hKL p hp
      ⟨hx _ hq.1, twist_eq_one μ w _ hq.2⟩

end GlobalTheory.CompanionTheory.ReadLevel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReversedProductSameSubquotients
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenRev

theorem isSubquotient_of_equiv {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G U}
    (h : IsSubquotient σ ρ) (E : ρ.Equiv ρ') : IsSubquotient σ ρ' :=
  h.trans (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective)

theorem isSubquotient_of_equiv_left {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (E : σ.Equiv τ) (h : IsSubquotient σ ρ) : IsSubquotient τ ρ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.surjective).trans h


set_option maxHeartbeats 2000000 in
theorem isSubquotient_prodIrr_rev : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k →
    ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Fin.rev a)).1 = N) {W : Type}
      [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible →
      IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Fin.rev a)) hd') := by
  intro k _ _ _ _ hA hGK h N x hd hd' W _ _ σ _ hi hsq

  obtain ⟨hdy, ⟨E1⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA (fun a => x (Fin.rev a)) hd'

  obtain ⟨hd2, ⟨E2⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse hA hGK (fun a => Zc.dualCl (x (Fin.rev a))) hdy
  have ex : (fun a => Zc.dualCl ((fun a => Zc.dualCl (x (Fin.rev a))) (Fin.rev a))) = x := funext fun a => by
    simp only [Fin.rev_rev]
    exact GlobalTheory.T.dual_class_involutive hA (x a)
  obtain ⟨E3⟩ := GlobalTheory.CompanionTheory.LSocle.prodIrr_congr ex hd2 hd
  have h1 : IsSubquotient σ ((prodIrr (fun a => Zc.dualCl (x (Fin.rev a))) hdy).comp (Zc.Cos.thetaW k N)) :=
    isSubquotient_of_equiv hsq (E2.trans E3).symm
  have h2 : IsSubquotient (σ.comp (Zc.Cos.thetaW k N)) (prodIrr (fun a => Zc.dualCl (x (Fin.rev a))) hdy) := by
    have := GlobalTheory.CompanionTheory.WordProd.RowCell.isSubquotient_pullback (Zc.Cos.thetaW k N) h1
    rwa [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW] at this
  have hs : IsSmooth (σ.comp (Zc.Cos.thetaW k N)) := h2.isSmooth (isSmooth_prodIrr _ _)
  have hi' : Representation.IsIrreducible (σ.comp (Zc.Cos.thetaW k N)) :=
    GlobalTheory.CosocleComp.isIrreducible_comp (GlobalTheory.CompanionTheory.LSocle.thetaW_surjective N) hi
  have h3 : IsSubquotient (σ.comp (Zc.Cos.thetaW k N)) (contra (prodIrr (fun a => x (Fin.rev a)) hd')) :=
    isSubquotient_of_equiv h2 E1.symm
  have h4 := _root_.GlobalTheory.CompanionTheory.ContraSq.contra_isSubquotient (GlobalTheory.SqIntUnit.compactOpen_basis k N) _ _ (isSmooth_contra _) h3
  obtain ⟨E4⟩ := GlobalTheory.T.double_contragredient_of_induced_product hA (fun a => x (Fin.rev a)) hd'
  obtain ⟨E5⟩ := GlobalTheory.CompanionTheory.LSocle.equiv_contra_comp_thetaW hGK σ hs hi'
  exact isSubquotient_of_equiv_left E5.symm (isSubquotient_of_equiv h4 E4)

end GlobalTheory.CompanionTheory.GenRev
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakeEigenvaluePairDecomposition
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS.SatConv

theorem esymm_cons_succ' (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

theorem coeff_prod_one_add (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + Polynomial.C a * Polynomial.X : Polynomial ℂ)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
    cases n with
    | zero => simp [ih, Multiset.esymm]
    | succ n => rw [Polynomial.coeff_X_mul, ih, ih, esymm_cons_succ']

theorem esymm_add_antidiagonal (s t : Multiset ℂ) (k : ℕ) :
    (s + t).esymm k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, s.esymm p.1 * t.esymm p.2 := by
  rw [← coeff_prod_one_add, Multiset.map_add (f := _), Multiset.prod_add, Polynomial.coeff_mul]
  simp only [coeff_prod_one_add]

theorem esymm_map_mul_unit (B : Multiset ℂˣ) (z : ℂˣ) (j : ℕ) :
    ((B.map (· * z)).map fun b : ℂˣ => (b : ℂ)).esymm j =
      (z : ℂ) ^ j * (B.map fun b : ℂˣ => (b : ℂ)).esymm j := by
  have h := Multiset.pow_smul_esymm (z : ℂ) j (B.map fun b : ℂˣ => (b : ℂ))
  simp only [smul_eq_mul, Multiset.map_map, Function.comp_def] at h
  simp only [Multiset.map_map, Function.comp_def, Units.val_mul, mul_comm _ (z : ℂ)]
  exact h.symm

theorem esymm_eq_zero_of_card_lt (s : Multiset ℂ) {k : ℕ} (h : s.card < k) : s.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

theorem satEig_join : ∀ (q n a b : ℕ) (c : ℂˣ) (Ba Bb : Multiset ℂˣ), q ≠ 0 → a + b = n → Ba.card = a → Bb.card = b → ∀ k ≤ n, satEig q n (Ba.map (· * c ^ b) + Bb.map (· * c ^ a)) k = ∑ p ∈ pairs a b k, coef q c a b p.1 p.2 * (satEig q a Ba p.1 * satEig q b Bb p.2) := by
  intro q n a b c Ba Bb hq hab hBa hBb k _
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  subst hab
  rw [pairs, Finset.sum_filter]
  simp only [satEig]
  rw [Multiset.map_add (f := _), esymm_add_antidiagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, j⟩ hp
  have hk : i + j = k := by simpa using hp
  subst hk
  simp only [esymm_map_mul_unit]
  split_ifs with h
  · have hpow : (q : ℂ) ^ ((((i + j : ℕ) : ℂ) * (((a + b : ℕ) : ℂ) - ((i + j : ℕ) : ℂ))) / 2) =
        (q : ℂ) ^ (((i : ℂ) * b + (j : ℂ) * a) / 2 - (i : ℂ) * j) *
          ((q : ℂ) ^ (((i : ℂ) * ((a : ℂ) - i)) / 2) * (q : ℂ) ^ (((j : ℂ) * ((b : ℂ) - j)) / 2)) := by
      rw [← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq']
      congr 1
      push_cast
      ring
    rw [hpow, coef]
    simp only [Units.val_pow_eq_pow_val]
    rw [pow_add, pow_mul, pow_mul, pow_right_comm (c : ℂ) i b, pow_right_comm (c : ℂ) j a]
    ring
  · have hz : (Ba.map fun x : ℂˣ => (x : ℂ)).esymm i = 0 ∨ (Bb.map fun x : ℂˣ => (x : ℂ)).esymm j = 0 := by
      by_cases hi : i ≤ a
      · right
        refine esymm_eq_zero_of_card_lt _ ?_
        rw [Multiset.card_map, hBb]
        by_contra hj
        exact h ⟨hi, by omega⟩
      · left
        refine esymm_eq_zero_of_card_lt _ ?_
        rw [Multiset.card_map, hBa]
        omega
    rcases hz with hz | hz <;> simp [hz]

end GlobalTheory.CompanionTheory.CtS.SatConv
end
end

