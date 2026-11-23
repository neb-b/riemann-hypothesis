module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0740
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0747
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasChartsOfForallIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedInverseOfLiftLocal
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB.GenInv

variable {A : Type} [CommRing A] {M M' : Type} [AddCommGroup M] [Module A M]
  [AddCommGroup M'] [Module A M']

noncomputable def proj (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) : M →ₗ[A] LinearMap.ker σ :=
  LinearMap.codRestrict _ (LinearMap.id - σ.smulRight v) (fun x => by
    simp [LinearMap.mem_ker, h])

theorem proj_coe (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) (x : M) :
    (proj σ v h x : M) = x - σ x • v := rfl

theorem proj_ker (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) (x : LinearMap.ker σ) :
    proj σ v h x = x :=
  Subtype.ext (by simp [proj_coe, LinearMap.mem_ker.1 x.2])

theorem apply_mem_smul_top (f : M →ₗ[A] M') (I : Ideal A) {x : M}
    (hx : x ∈ I • (⊤ : Submodule A M)) : f x ∈ I • (⊤ : Submodule A M') := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem ker_finite [Module.Finite A M] (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) :
    Module.Finite A (LinearMap.ker σ) :=
  Module.Finite.of_surjective (proj σ v h) (fun x => ⟨x, proj_ker σ v h x⟩)

theorem ker_free [IsLocalRing A] [Module.Finite A M] [Module.Free A M] (σ : M →ₗ[A] A) (v : M)
    (h : σ v = 1) : Module.Free A (LinearMap.ker σ) := by
  haveI := ker_finite σ v h
  haveI : Module.Projective A (LinearMap.ker σ) :=
    Module.Projective.of_split (LinearMap.ker σ).subtype (proj σ v h)
      (LinearMap.ext fun x => proj_ker σ v h x)
  haveI : Module.FinitePresentation A (LinearMap.ker σ) :=
    Module.finitePresentation_of_projective _ _
  exact Module.free_of_flat_of_isLocalRing

noncomputable def kerEquiv (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) :
    M ≃ₗ[A] A × LinearMap.ker σ :=
  LinearEquiv.ofLinear (σ.prod (proj σ v h))
    (LinearMap.coprod (LinearMap.toSpanSingleton A M v) (LinearMap.ker σ).subtype)
    (by
      ext x
      · simp [h]
      · simp [proj_coe, h]
      · simp [LinearMap.mem_ker.1 x.2]
      · simp [proj_coe, LinearMap.mem_ker.1 x.2])
    (by
      ext x
      simp [proj_coe])

theorem finrank_ker [IsLocalRing A] [Module.Finite A M] [Module.Free A M] (σ : M →ₗ[A] A) (v : M)
    (h : σ v = 1) : Module.finrank A M = 1 + Module.finrank A (LinearMap.ker σ) := by
  haveI := ker_finite σ v h
  haveI := ker_free σ v h
  rw [(kerEquiv σ v h).finrank_eq, Module.finrank_prod, Module.finrank_self]

theorem exists_form [IsLocalRing A] [Module.Finite A M] [Module.Free A M] (y : M)
    (hy : y ∉ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) :
    ∃ σ : M →ₗ[A] A, σ y = 1 := by
  classical
  let e := Module.Free.chooseBasis A M
  by_cases h : ∀ i, e.repr y i ∈ IsLocalRing.maximalIdeal A
  · refine absurd ?_ hy
    rw [← e.sum_repr y]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) trivial
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    have hu : IsUnit (e.repr y i) := by
      by_contra hn
      exact hi ((IsLocalRing.mem_maximalIdeal _).2 hn)
    obtain ⟨u, hu⟩ := hu
    refine ⟨((↑u⁻¹ : A)) • e.coord i, ?_⟩
    simp [← hu]

noncomputable def restr (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) :
    LinearMap.ker (σ ∘ₗ b) →ₗ[A] LinearMap.ker σ :=
  b.restrict (fun x hx => by simpa using hx)

theorem restr_coe (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) (x : LinearMap.ker (σ ∘ₗ b)) :
    (restr b σ x : M') = b x := rfl

theorem restr_proj (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) (x₀ : M) (h : σ (b x₀) = 1) (q : M) :
    restr b σ (proj (σ ∘ₗ b) x₀ h q) = proj σ (b x₀) h (b q) :=
  Subtype.ext (by simp [restr_coe, proj_coe])

theorem lift_restr [IsLocalRing A] (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) (x₀ : M)
    (h : σ (b x₀) = 1) (hb : Lift b) : Lift (restr b σ) := by
  intro J t hJ ht z hz
  obtain ⟨x, hx, hxz⟩ := hb J t hJ ht z (apply_mem_smul_top (LinearMap.ker σ).subtype _ hz)
  refine ⟨proj (σ ∘ₗ b) x₀ h x, ?_, ?_⟩
  · rw [restr_proj]
    exact apply_mem_smul_top (proj σ (b x₀) h) _ hx
  · have e : proj (σ ∘ₗ b) x₀ h x - z = proj (σ ∘ₗ b) x₀ h (x - z) := by
      rw [map_sub, proj_ker]
    rw [e]
    exact apply_mem_smul_top _ _ hxz

theorem generalized_inverse_of_lift_rank [IsLocalRing A] : ∀ (n : ℕ) (Q N : Type) [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Free A Q] [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Free A N] (b : Q →ₗ[A] N), Module.finrank A N = n → Lift b →
    ∃ s : N →ₗ[A] Q, b ∘ₗ s ∘ₗ b = b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q N _ _ _ _ _ _ _ _ b hn hb
    by_cases h : ∀ q, b q ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A N)
    · refine ⟨0, ?_⟩
      rw [GlobalTheory.T.lift_reduction_zero_of_maximal A Q N b hb h]
      simp
    · push_neg at h
      obtain ⟨x₀, hx₀⟩ := h
      obtain ⟨σ, hσ⟩ := exists_form _ hx₀
      have hσ' : (σ ∘ₗ b) x₀ = 1 := hσ
      haveI := ker_finite σ (b x₀) hσ
      haveI := ker_free σ (b x₀) hσ
      haveI := ker_finite (σ ∘ₗ b) x₀ hσ'
      haveI := ker_free (σ ∘ₗ b) x₀ hσ'
      have hlt : Module.finrank A (LinearMap.ker σ) < n := by
        have := finrank_ker σ (b x₀) hσ
        omega
      obtain ⟨s₁, hs₁⟩ := ih _ hlt (LinearMap.ker (σ ∘ₗ b)) (LinearMap.ker σ) (restr b σ) rfl
        (lift_restr b σ x₀ hσ hb)
      refine ⟨σ.smulRight x₀ + (LinearMap.ker (σ ∘ₗ b)).subtype ∘ₗ s₁ ∘ₗ proj σ (b x₀) hσ, ?_⟩
      ext q
      have h1 : restr b σ (s₁ (restr b σ (proj (σ ∘ₗ b) x₀ hσ' q))) =
          restr b σ (proj (σ ∘ₗ b) x₀ hσ' q) := LinearMap.congr_fun hs₁ _
      rw [restr_proj] at h1
      have h2 := congrArg (Subtype.val) h1
      rw [restr_coe, proj_coe] at h2
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, map_add (f := _),
        map_smul, Submodule.subtype_apply]
      rw [h2]
      abel

end GlobalTheory.CompanionTheory.PerfVB.GenInv

theorem GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift :
    ∀ (A Q N : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
      [Module.Free A Q] [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Free A N]
      (b : Q →ₗ[A] N), Lift b → ∃ s : N →ₗ[A] Q, b ∘ₗ s ∘ₗ b = b :=
  fun A Q N _ _ _ _ _ _ _ _ _ _ b hb =>
    GenInv.generalized_inverse_of_lift_rank (A := A) _ Q N b rfl hb
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasCompactSupportTj
section
open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtHecke

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isUnifV_of_ordL {w : Pl E} {x : w.adicCompletion E} (h0 : x ≠ 0) (h : ordL x = 1) : IsUnifV E w x := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  unfold ordL at h
  rw [dite_eq_right hv] at h
  have e : WithZero.unzero hv = Multiplicative.ofAdd (-1 : ℤ) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    omega
  unfold IsUnifV
  rw [← e, WithZero.coe_unzero]

theorem ordL_eq_zero {w : Pl E} {x : w.adicCompletion E} (h : Valued.v x = 1) : ordL x = 0 := by
  have hv : Valued.v x ≠ 0 := by rw [h]; exact one_ne_zero
  unfold ordL
  rw [dite_eq_right hv]
  have e : WithZero.unzero hv = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  rw [e]
  simp

theorem det_mem {w : Pl E} {n : ℕ} {M : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hM : ∀ i j, M i j ∈ Ov E w) : M.det ∈ Ov E w := by
  rw [Matrix.det_apply']
  exact Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _)
    (Subring.prod_mem _ fun i _ => hM _ _)

theorem v_det {w : Pl E} {n : ℕ} {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v g.val.det = 1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hg
  have d1 : Valued.v g.val.det ≤ 1 := det_mem h1
  have d2 : Valued.v (g⁻¹).val.det ≤ 1 := det_mem h2
  have e : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, show g.val * (g⁻¹).val = 1 from g.mul_inv, Matrix.det_one]
  have e' : Valued.v g.val.det * Valued.v (g⁻¹).val.det = 1 := by
    rw [← map_mul, e, map_one]
  refine le_antisymm d1 ?_
  calc (1 : _) = Valued.v g.val.det * Valued.v (g⁻¹).val.det := e'.symm
    _ ≤ Valued.v g.val.det * 1 := mul_le_mul_right d2 _
    _ = _ := mul_one _

def cMu {a b : ℕ} {w : Pl E} (μ : (w.adicCompletion E)ˣ →* ℂˣ) (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ)

theorem mu_unit {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1)
    {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) :
    μ (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) = 1 := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hκ
  refine hμ _ (ordL_eq_zero ?_)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, map_mul, map_pow,
    v_det h1, v_det h2, one_pow, one_mul]

theorem cMu_mul_left {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1)
    {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) (m : GLw a w × GLw b w) : cMu μ (κ * m) = cMu μ m := by
  unfold cMu
  have e : ((-1) ^ (a * b) * GeneralLinearGroup.det (κ * m).1 ^ b * GeneralLinearGroup.det (κ * m).2 ^ a :
      (w.adicCompletion E)ˣ) = ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) *
        (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
    ac_rfl
  rw [e, map_mul, mu_unit hμ hκ, mul_one]

theorem cMu_mul_right {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1)
    {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) (m : GLw a w × GLw b w) : cMu μ (m * κ) = cMu μ m := by
  unfold cMu
  have e : ((-1) ^ (a * b) * GeneralLinearGroup.det (m * κ).1 ^ b * GeneralLinearGroup.det (m * κ).2 ^ a :
      (w.adicCompletion E)ˣ) = ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) *
        (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
    ac_rfl
  rw [e, map_mul, mu_unit hμ hκ, mul_one]

theorem hasCompactSupport_Tj {w : Pl E} {n : ℕ} {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (k : ℕ) :
    HasCompactSupport (Tj ℂ n (Ov E w) ϖ k : GLw n w → ℂ) := by
  have hdet : (diagJ n ϖ k).det ≠ 0 := by
    rw [diagJ, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs
    · exact h0
    · exact one_ne_zero
  set t : GLw n w := GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ k) hdet with ht
  have hI := GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w n
  have hS : IsCompact ((fun p : GLw n w × GLw n w => p.1 * t * p.2) ''
      ((GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ×ˢ (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)))) :=
    (hI.prod hI).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  refine HasCompactSupport.intro' hS hS.isClosed fun g hg => ?_
  unfold Tj
  refine Set.indicator_of_notMem ?_ _
  rintro ⟨x, hx, y, hy, e⟩
  exact hg ⟨(x, y), ⟨hx, hy⟩, Units.ext (by simpa [ht] using e.symm)⟩

theorem blk_zero_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) :
    blk h w κ 0 ∈ GlobalTheory.LFun.KGL w (n := n) := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hκ
  obtain ⟨l1, l2⟩ := GlobalTheory.BCT.CtLevel.lev_KGL_of_unram E a b n h w 1 (fun _ _ => rfl)
  have d1 : GlobalTheory.BCT.CtLevel.dgM h w (κ.1, 1) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have : κ.1 ∈ GlobalTheory.BCT.CtLevel.lev₁ h w (GlobalTheory.LFun.KGL w (n := n)) 1 := by rw [l1]; exact h1
    exact this.1.2
  have d2 : GlobalTheory.BCT.CtLevel.dgM h w (1, κ.2) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have : κ.2 ∈ GlobalTheory.BCT.CtLevel.lev₂ h w (GlobalTheory.LFun.KGL w (n := n)) 1 := by rw [l2]; exact h2
    exact this.1.2
  rw [GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blk_zero_eq]
  have e : κ = (κ.1, 1) * (1, κ.2) := by simp
  rw [e, map_mul]
  exact mul_mem d1 d2

theorem ctT_eq {n a b : ℕ} (h : a + b = n) {w : Pl E} (hw : IsSplitAt w) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (k : ℕ) :
    RS.ctT h w μ ϖ k = fun m => cMu μ m * phi3 h w (Tj ℂ n (Ov E w) ϖ k) 1 1 m := by
  funext m
  rw [GlobalTheory.CompanionTheory.CtS.ctT_split_eq E n a b h w μ ϖ hw hϖ k m]
  simp [phi3, cMu]

theorem isHecke_ctT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : (w.adicCompletion E)ˣ), IsSplitAt w → ordL (ϖ : w.adicCompletion E) = 1 → (∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) → ∀ k : ℕ, IsHecke (K2 a b w) (RS.ctT h w μ (ϖ : w.adicCompletion E) k) := by
  intro E _ _ _ n a b h w μ ϖ hw hord hμ k
  have h0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  have hϖ : IsUnifV E w (ϖ : w.adicCompletion E) := isUnifV_of_ordL h0 hord
  have hT := Tj_mem_hecke (n := n) hϖ k
  have hf : ∀ k₁ ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k₂ ∈ GlobalTheory.LFun.KGL w (n := n), ∀ g : GLw n w,
      Tj ℂ n (Ov E w) (ϖ : w.adicCompletion E) k (k₁ * g * k₂) = Tj ℂ n (Ov E w) (ϖ : w.adicCompletion E) k g :=
    fun k₁ h₁ k₂ h₂ g => hT.1 ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ g
  have hbi := GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_bi_invariant (a := a) (b := b) h w (GlobalTheory.LFun.KGL w (n := n)) le_rfl
    (fun k hk k' hk' => mul_mem (mul_mem hk hk') (inv_mem hk)) _ hf 1 1 (one_mem _) (one_mem _)
  have hone : (1 : GLw a w × GLw b w) ∈ leviOf h w (GlobalTheory.LFun.KGL w (n := n)) := blk_zero_mem h w (one_mem _)
  rw [ctT_eq h hw μ hϖ k]
  refine ⟨?_, fun κ hκ x => ⟨?_, ?_⟩⟩
  · exact (GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_compact_support h w _ (hasCompactSupport_Tj h0 k) 1 1).mul_left
  · have := hbi κ 1 (blk_zero_mem h w hκ) hone x
    rw [mul_one] at this
    simp only [cMu_mul_left hμ hκ, this]
  · have := hbi 1 κ hone (blk_zero_mem h w hκ) x
    rw [one_mul] at this
    simp only [cMu_mul_right hμ hκ, this]

end GlobalTheory.CompanionTheory.CtHecke
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFiniteFlat
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open GlobalTheory.CompanionTheory.Ar.GR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.KerFF

variable {R : Type} [CommRing R]

theorem exists_sp_iso (X : Over (Sp R)) [IsFinite X.hom] [Flat X.hom] [LocallyOfFinitePresentation X.hom] :
    ∃ (F : Type) (_ : CommRing F) (_ : Algebra R F) (_ : Nonempty (sp (R₀ := R) F ≅ X)),
      Module.Finite R F ∧ Module.Projective R F := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  have f₁ : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have f₂ : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have f₃ : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at f₁
  rw [Flat.SpecMap_iff] at f₂
  rw [LocallyOfFinitePresentation.SpecMap_iff] at f₃
  letI : Algebra R Γ(X.left, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite R Γ(X.left, ⊤) := RingHom.finite_algebraMap.1 f₁
  haveI : Module.Flat R Γ(X.left, ⊤) := RingHom.flat_algebraMap_iff.1 f₂
  haveI : Algebra.FinitePresentation R Γ(X.left, ⊤) := RingHom.finitePresentation_algebraMap.1 f₃
  haveI : Module.FinitePresentation R Γ(X.left, ⊤) := Module.FinitePresentation.of_finite_of_finitePresentation _ _
  refine ⟨Γ(X.left, ⊤), inferInstance, inferInstance,
    ⟨Over.isoMk X.left.isoSpec.symm ?_⟩, inferInstance, Module.Flat.projective_of_finitePresentation⟩
  exact hφ.symm

theorem mul_comp_hom {A B T : Over (Sp R)} [GrpObj A] [GrpObj B] (u v : T ⟶ A) (l : A ⟶ B) [IsMonHom l] :
    (u * v) ≫ l = (u ≫ l) * (v ≫ l) := by
  rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem one_comp_hom {A B T : Over (Sp R)} [GrpObj A] [GrpObj B] (l : A ⟶ B) [IsMonHom l] :
    (1 : T ⟶ A) ≫ l = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem kernelFinFlat : PositivityTheory.Tls2.Zar3.Ch1.KernelFinFlat := by
  intro R _ A B _ _ l hA hB hl hfin hflat
  haveI := hA.smooth
  haveI := hB.smooth
  haveI : IsFinite l.left := hfin
  haveI : Flat l.left := hflat
  haveI : IsMonHom l := hl
  have hw : l.left ≫ B.hom = A.hom := Over.w l
  haveI : LocallyOfFinitePresentation (l.left ≫ B.hom) := by rw [hw]; infer_instance
  haveI : LocallyOfFinitePresentation l.left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp l.left B.hom
  let e : Sp R ⟶ B.left := (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left
  have he : e ≫ B.hom = 𝟙 _ := Over.w (η[B] : 𝟙_ (Over (Sp R)) ⟶ B)
  haveI : Mono e := mono_of_mono_fac he
  let X : Over (Sp R) := Over.mk (pullback.snd l.left e)
  haveI : IsFinite X.hom := inferInstanceAs (IsFinite (pullback.snd l.left e))
  haveI : Flat X.hom := inferInstanceAs (Flat (pullback.snd l.left e))
  haveI : LocallyOfFinitePresentation X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd l.left e))
  have hf : pullback.fst l.left e ≫ A.hom = X.hom := by
    rw [← hw, pullback.condition_assoc, he, Category.comp_id]
    rfl
  let f : X ⟶ A := Over.homMk (pullback.fst l.left e) hf
  have key : ∀ (T : Over (Sp R)) (z : T ⟶ A), z ≫ l = 1 ↔ ∃ t : T ⟶ X, t ≫ f = z := by
    intro T z
    have one_left : (1 : T ⟶ B).left = T.hom ≫ e := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    constructor
    · intro h
      have h' : z.left ≫ l.left = T.hom ≫ e := by
        rw [← one_left, ← h, Over.comp_left]
      refine ⟨Over.homMk (pullback.lift z.left T.hom h') (pullback.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    · rintro ⟨t, rfl⟩
      apply Over.OverMorphism.ext
      rw [one_left, ← Over.w t]
      change (t.left ≫ pullback.fst l.left e) ≫ l.left = (t.left ≫ pullback.snd l.left e) ≫ e
      rw [Category.assoc, Category.assoc, pullback.condition]
  have fmono : ∀ {T : Over (Sp R)} (t t' : T ⟶ X), t ≫ f = t' ≫ f → t = t' := by
    intro T t t' h
    apply Over.OverMorphism.ext
    rw [← cancel_mono (pullback.fst l.left e)]
    exact congrArg (fun u => u.left) h
  obtain ⟨F, iF, aF, ⟨ee⟩, hfinF, hproj⟩ := exists_sp_iso X
  have ker : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A),
      z ≫ l = 1 ↔ ∃ φ : F →ₐ[R] S, spMap φ ≫ (ee.hom ≫ f) = z := by
    intro S _ _ z
    rw [key]
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨φ, hφ⟩ := GlobalTheory.NatFun.spMap_surjective (k := R) (A := F) (B := S) (t ≫ ee.inv)
      exact ⟨φ, by rw [hφ]; simp⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨spMap φ ≫ ee.hom, by simp⟩
  refine ⟨F, iF, aF, ee.hom ≫ f, ⟨hproj, hfinF, ?_, ?_, ?_, ?_⟩, ker⟩
  · intro S _ _ φ φ' h
    apply GlobalTheory.NatFun.spMap_injective (k := R) (A := F) (B := S)
    have h₁ : (spMap φ ≫ ee.hom) ≫ f = (spMap φ' ≫ ee.hom) ≫ f := by simpa using h
    exact (cancel_mono ee.hom).1 (fmono _ _ h₁)
  · intro S _ _
    exact (ker S 1).1 (one_comp_hom l)
  · intro S _ _ φ φ'
    exact (ker S _).1 (by
      rw [mul_comp_hom, (ker S _).2 ⟨φ, rfl⟩, (ker S _).2 ⟨φ', rfl⟩, _root_.mul_one])
  · intro S _ _ φ
    have hz := (ker S _).2 ⟨φ, rfl⟩
    have h₂ : (spMap φ ≫ ee.hom ≫ f)⁻¹ ≫ l = 1 := by
      have h₃ := mul_comp_hom (spMap φ ≫ ee.hom ≫ f)⁻¹ (spMap φ ≫ ee.hom ≫ f) l
      rw [inv_mul_cancel, one_comp_hom, hz, _root_.mul_one] at h₃
      exact h₃.symm
    obtain ⟨χ, hχ⟩ := (ker S _).1 h₂
    exact ⟨χ, by rw [hχ, inv_mul_cancel]⟩

end GlobalTheory.CompanionTheory.Ar.KerFF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSplitOf
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
open PositivityTheory.Rg.BcB.F.Eig (lconv)
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace GlobalTheory.CompanionTheory.MatchPowers

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isLevel_KL (n : ℕ) (w : Pl E) : IsLevel (MonoidHom.id _) (KL n w) (KL n w) :=
  ⟨GlobalTheory.CompanionTheory.SphLine.isOpen_KL n w, le_rfl, fun _ h => h⟩

theorem isHecke_lpow_KL {n : ℕ} {w : Pl E} {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) (j : ℕ) :
    IsHecke (KL n w) (lpow (KL n w) f j) :=
  GlobalTheory.CompanionTheory.UnitaryWord.isHecke_lpow GlobalTheory.CompanionTheory.LocHecke.locAlg (isLevel_KL n w) hf j

theorem matchSplitOf : MatchSplitOf := by
  intro hM3 hCt E _ _ _ n a ha w hw μ hμ f hf k hk
  have hc : ∀ j : ℕ, ctMu (Nat.add_sub_cancel' ha) w μ (lpow (KL n w) f j) =
      Nat.rec (ctMu (Nat.add_sub_cancel' ha) w μ (lone (KL n w)))
        (fun _ g => mconv (ctMu (Nat.add_sub_cancel' ha) w μ f) g) j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have h := hCt E n a ha w hw μ hμ f _ hf (isHecke_lpow_KL hf j)
      rw [ih] at h
      exact h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := hM3 E n a ha w hw μ (KL n w) (isLevel_KL n w) _ (isHecke_lpow_KL hf (j + 1))
  rw [hc (j + 1)] at h
  exact h

end GlobalTheory.CompanionTheory.MatchPowers

end
end

