module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0733
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicVectorIntertwinerDetermined
section
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA

theorem lower_bound_of_cyclic_coef : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ), 0 < d → IsU σ → IsU ρ →
    ∀ (w₀ : A) (v : B) (i : A →L[ℂ] B), IsMap σ ρ i → (Submodule.span ℂ (Set.range fun x => σ x w₀)).topologicalClosure = ⊤ →
    ∀ (T : A →L[ℂ] A) (E : B →L[ℂ] B), (∀ x y, ⟪σ x w₀, T (σ y w₀)⟫_ℂ = star ⟪ρ x⁻¹ v, E (ρ y⁻¹ v)⟫_ℂ) →
    (∀ z, ‖⟪z, i w₀⟫_ℂ‖ ^ 2 / d ≤ (⟪z, E z⟫_ℂ).re) → ∀ a, ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re := by
  intro Γ _ _ A B _ _ _ _ _ _ σ ρ d hd hσ hρ w₀ v i hi hcyc T E hTE hE a
  obtain ⟨h1, hmul, hnorm, -⟩ := hρ
  have hρinner : ∀ (g : Γ) (x y : B), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    (LinearIsometry.mk (ρ g : B →ₗ[ℂ] B) (hnorm g)).inner_map_map x y
  have hadj : ∀ (g : Γ) (x y : B), ⟪ρ g⁻¹ x, y⟫_ℂ = ⟪x, ρ g y⟫_ℂ := by
    intro g x y
    rw [← hρinner g (ρ g⁻¹ x) y]
    congr 1
    rw [← ContinuousLinearMap.mul_apply, ← hmul, mul_inv_cancel, h1, ContinuousLinearMap.one_apply]
  have hi' : ∀ (g : Γ) (x : A), i (σ g x) = ρ g (i x) := hi
  have hTE' : ∀ x y, ⟪σ x w₀, T (σ y w₀)⟫_ℂ = starRingEnd ℂ ⟪ρ x⁻¹ v, E (ρ y⁻¹ v)⟫_ℂ :=
    fun x y => (hTE x y).trans (starRingEnd_apply _).symm
  have hclosed : IsClosed {a : A | ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re} := by
    apply isClosed_le
    · exact ((continuous_const.inner i.continuous).norm.pow 2).div_const d
    · exact Complex.continuous_re.comp (continuous_id.inner T.continuous)
  have hspan : (Submodule.span ℂ (Set.range fun x => σ x w₀) : Set A) ⊆
      {a : A | ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re} := by
    intro a ha
    rw [SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp] at ha
    obtain ⟨c, rfl⟩ := ha
    set z : B := c.sum fun y t => starRingEnd ℂ t • ρ y⁻¹ v with hz
    have h1' : ⟪v, i (c.sum fun x t => t • σ x w₀)⟫_ℂ = ⟪z, i w₀⟫_ℂ := by
      rw [hz]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finsupp.sum, map_sum, map_smul, inner_sum, sum_inner, inner_smul_right,
        inner_smul_left, hi', hadj, Complex.conj_conj, RCLike.conj_conj, starRingEnd_self_apply]
    have h2' : ⟪c.sum fun x t => t • σ x w₀, T (c.sum fun x t => t • σ x w₀)⟫_ℂ =
        starRingEnd ℂ ⟪z, E z⟫_ℂ := by
      rw [hz]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finsupp.sum, map_sum, map_smul, inner_sum, sum_inner, inner_smul_right,
        inner_smul_left, hTE', map_mul, Complex.conj_conj, RCLike.conj_conj, starRingEnd_self_apply]
    rw [Set.mem_setOf_eq, h1', h2', Complex.conj_re]
    exact hE z
  have ha : a ∈ closure (Submodule.span ℂ (Set.range fun x => σ x w₀) : Set A) := by
    rw [← Submodule.topologicalClosure_coe, hcyc]
    simp
  exact closure_minimal hspan hclosed ha

end GlobalTheory.CompanionTheory.RgHeA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinCohStOfCmpSt
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Hodge

theorem finCohSt_of_cmpSt : CmpSt → FinCohSt := by
  intro h R _ _ X s _ P _ _ S
  letI := GlobalTheory.algebraΓOfHom s
  have hf : ∀ p, Module.Finite R (GlobalTheory.coh (GlobalTheory.structureModule X) p) := fun p ↦
    GlobalTheory.ProperFinite.finite_coh_of_isProper s (GlobalTheory.structureModule X) p
  obtain ⟨⟨e₀⟩, hn⟩ := h R X s inferInstance P S
  refine ⟨?_, fun n ↦ ?_⟩
  · have := hf 0
    exact Module.Finite.equiv e₀.symm
  · obtain ⟨e⟩ := hn n
    have := hf (n + 1)
    exact Module.Finite.equiv e.symm

end GlobalTheory.CompanionTheory.Hodge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstHypercohomologyBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.HodgeAssembly

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem clForm_injective (s : X ⟶ Sp R) (hS : Stein (OAff s)) : Function.Injective (clForm s) := by
  refine (injective_iff_map_eq_zero _).2 fun ω h ↦ ?_
  obtain ⟨g, hg, hD⟩ := ofForm_eq_zero.1 h
  have h0 : d0 (OAff s) g = 0 := by
    funext T T' φ
    exact sub_eq_zero.2 (hg φ)
  obtain ⟨r, rfl⟩ := (hS.1 g).1 h0
  refine Subtype.ext (Subtype.ext (funext fun T ↦ ?_))
  refine (hD T).symm.trans ?_
  exact Derivation.map_algebraMap _ r

theorem vb_middle {M N P : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P]
    [Module R P] (i : M →ₗ[R] N) (q : N →ₗ[R] P) (hi : Function.Injective i) (hq : Function.Surjective q)
    (hex : Function.Exact i q) {a b : ℕ} (hM : VB R M a) (hP : VB R P b) : VB R N (a + b) := by
  obtain ⟨f1, f2, f3⟩ := hM
  obtain ⟨g1, g2, g3⟩ := hP
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property q LinearMap.id hq
  let e : N ≃ₗ[R] M × P := (hex.splitSurjectiveEquiv hi ⟨σ, hσ⟩).1
  refine ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun p ↦ ?_⟩
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod, Pi.add_apply, f3, g3]

theorem exists_abelian {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {s' : X' ⟶ S'}
    {φ : X' ⟶ A.left} {f : S' ⟶ S} (h : IsPullback φ s' A.hom f) :
    ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') := by
  let e : Over.mk s' ≅ (Over.pullback f).obj A := Over.isoMk h.isoPullback h.isoPullback_hom_snd
  let I : GrpObj (Over.mk s') := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  exact ⟨I, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A f))⟩

theorem bijective_middle {M N P M' N' P' : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    [AddCommGroup P'] [Module R P'] (i : M →ₗ[R] N) (q : N →ₗ[R] P) (i' : M' →ₗ[R] N') (q' : N' →ₗ[R] P')
    (L : N →ₗ[R] N') (eM : M ≃ₗ[R] M') (eP : P ≃ₗ[R] P') (hex : Function.Exact i q)
    (hq : Function.Surjective q) (hex' : Function.Exact i' q') (hi' : Function.Injective i')
    (s₁ : ∀ m, L (i m) = i' (eM m)) (s₂ : ∀ n, q' (L n) = eP (q n)) : Function.Bijective L := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, fun x ↦ ?_⟩
  · have h1 : q z = 0 := by
      apply eP.injective
      rw [← s₂, hz, map_zero, map_zero]
    obtain ⟨m, rfl⟩ := (hex z).1 h1
    have h2 : eM m = 0 := hi' (by rw [← s₁, hz, map_zero])
    rw [(map_eq_zero_iff eM eM.injective).1 h2, map_zero]
  · obtain ⟨z, hz⟩ := hq (eP.symm (q' x))
    have h1 : q' (x - L z) = 0 := by
      rw [map_sub, s₂, hz, LinearEquiv.apply_symm_apply, sub_self]
    obtain ⟨m', hm'⟩ := (hex' _).1 h1
    refine ⟨z + i (eM.symm m'), ?_⟩
    rw [map_add (f := _), s₁, LinearEquiv.apply_symm_apply, hm']
    abel

section BaseChange

variable [Algebra R R'] {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}

def clG (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) : GlobForm s →ₗ[R] HH1 s :=
  clForm s ∘ₗ (LinearEquiv.ofTop _ hcl).symm.toLinearMap

theorem clG_injective (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) (hi : Function.Injective (clForm s)) :
    Function.Injective (clG s hcl) :=
  hi.comp (LinearEquiv.ofTop _ hcl).symm.injective

theorem exact_clG (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) : Function.Exact (clG s hcl) (toHO1 s) := by
  intro c
  change c ∈ CechHodgeFiltration s ↔ _
  rw [cechHodgeFiltration_eq_range]
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨ω.1, congrArg (clForm s) (Subtype.ext rfl)⟩
  · rintro ⟨ω, rfl⟩
    exact ⟨_, rfl⟩

theorem first_hypercohomology_base_change (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) (hcl : ClosedForm s = ⊤)
    (hcl' : ClosedForm s' = ⊤) (hsurj : Function.Surjective (toHO1 s))
    (hinj' : Function.Injective (clForm s'))
    (eF : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s') (hF : ∀ c, IsPullForm w c (eF (1 ⊗ₜ c)))
    (eO : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s') (hO : ∀ c, IsPullO w c (eO (1 ⊗ₜ c))) :
    ∃ e : R' ⊗[R] HH1 s ≃ₗ[R'] HH1 s', ∀ c, IsPull1 w c (e (1 ⊗ₜ c)) := by
  let L : R' ⊗[R] HH1 s →ₗ[R'] HH1 s' := GlobalTheory.DeRham.liftSemi (pullHH1 w)
  have hL : ∀ c, L (1 ⊗ₜ c) = pullHH1 w c := fun c ↦ by
    rw [show L (1 ⊗ₜ c) = (1 : R') • pullHH1 w c from rfl, one_smul]
  have k₁ : ∀ ω, pullHH1 w (clG s hcl ω) = clG s' hcl' (eF (1 ⊗ₜ ω)) := fun ω ↦
    (IsPull1.eq_pullHH1 w (IsPullForm.cl (ω := ⟨ω, hcl ▸ trivial⟩)
      (ω' := ⟨eF (1 ⊗ₜ ω), hcl' ▸ trivial⟩) (hF ω))).symm
  have k₂ : ∀ c, toHO1 s' (pullHH1 w c) = eO (1 ⊗ₜ toHO1 s c) := fun c ↦
    (IsPullO.eq_pullHO1 w (IsPull1.toO (isPull1_pullHH1 w c))).trans
      (IsPullO.eq_pullHO1 w (hO (toHO1 s c))).symm
  have hex : Function.Exact ((clG s hcl).baseChange R') ((toHO1 s).baseChange R') := by
    have := lTensor_exact R' (exact_clG s hcl) hsurj
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hq : Function.Surjective ((toHO1 s).baseChange R') := by
    have := LinearMap.lTensor_surjective R' hsurj
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hb : Function.Bijective L := by
    refine bijective_middle ((clG s hcl).baseChange R') ((toHO1 s).baseChange R') (clG s' hcl') (toHO1 s') L eF eO
      hex hq (exact_clG s' hcl') (clG_injective s' hcl' hinj') (fun m ↦ ?_) fun n ↦ ?_
    · induction m using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul x ω =>
        have e : x ⊗ₜ[R] ω = x • ((1 : R') ⊗ₜ[R] ω) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [LinearMap.baseChange_tmul, e, map_smul, map_smul, ← k₁]
        rw [show L (x ⊗ₜ clG s hcl ω) = x • pullHH1 w (clG s hcl ω) from rfl]
    · induction n using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul x c =>
        have e : x ⊗ₜ[R] toHO1 s c = x • ((1 : R') ⊗ₜ[R] toHO1 s c) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [LinearMap.baseChange_tmul, e, map_smul, ← k₂]
        rw [show L (x ⊗ₜ c) = x • pullHH1 w c from rfl, map_smul]
  refine ⟨LinearEquiv.ofBijective L hb, fun c ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, hL]
  exact isPull1_pullHH1 w c

end BaseChange

theorem abelianHodgeDeRham_of_statements : SteinSt → ParSt → H1StructureBundle → DegenSt → WedgeHypSt → OBCSt → FormBCSt →
    GlobalTheory.Published.AbelianHodgeDeRham := by
  intro hS hP hH hD hW hO hF R _ A _ g hA hg
  have s₀ : Stein (OAff A.hom) := hS R A g hA hg
  have p₀ : VB R (GlobForm A.hom) g := (hP R A g hA hg).2
  have h₀ : VB R (HO1 A.hom) g := hH R A g hA hg
  obtain ⟨hcl, hsurj⟩ : ClosedForm A.hom = ⊤ ∧ Function.Surjective (toHO1 A.hom) := hD R A g hA hg
  have hinj := clForm_injective A.hom s₀
  have v : VB R (HH1 A.hom) (g + g) := vb_middle (clG A.hom hcl) (toHO1 A.hom) (clG_injective A.hom hcl hinj) hsurj
    (exact_clG A.hom hcl) p₀ h₀
  refine ⟨⟨v.1, v.2.1, fun p ↦ by rw [two_mul]; exact v.2.2 p⟩, hW R A g hA hg, p₀, h₀, ⟨hcl, hinj, hsurj⟩,
    fun R' _ _ X' s' φ h ↦ ?_⟩
  obtain ⟨eO, heO⟩ := hO R A g hA hg R' X' s' φ h
  obtain ⟨eF, heF⟩ := hF R A g hA hg R' X' s' φ h
  obtain ⟨_, hA'⟩ := exists_abelian A hA h
  have hg' : SmoothOfRelativeDimension g (Over.mk s').hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg
  have s₁ : Stein (OAff s') := hS R' (Over.mk s') g hA' hg'
  have hcl' : ClosedForm s' = ⊤ := (hD R' (Over.mk s') g hA' hg').1
  exact ⟨first_hypercohomology_base_change h.w hcl hcl' hsurj (clForm_injective s' s₁) eF heF eO heO, ⟨eF, heF⟩, ⟨eO, heO⟩⟩

end GlobalTheory.CompanionTheory.HodgeAssembly
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalDegreeMatrixCoefficientNorm
section
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeA.CoefHS

section SlopeTestRemainingChoices

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  {ν : Measure Γ} {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]

theorem memLp_coef {σ : Γ → (A →L[ℂ] A)} (hσ : IsU σ) {d : ℝ} (hd : IsFd ν σ d) (w v : A) :
    MemLp (fun g => ⟪w, σ g v⟫_ℂ) 2 ν := by
  have hm : AEStronglyMeasurable (fun g => ⟪w, σ g v⟫_ℂ) ν :=
    (continuous_const.inner (hσ.cont v)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine ((hd.2 v w v w).1.norm).congr (.of_forall fun g => ?_)
  simp only [norm_mul, norm_star, sq]

theorem memLp_diag {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν) : MemLp (fun g => ⟪v, ρ g v⟫_ℂ) 2 ν := by
  have hc : Continuous fun g => ⟪v, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 ?_
  refine (hm.norm.mul_const (‖v‖ * ‖v‖)).mono' (hc.norm.pow 2).aestronglyMeasurable (.of_forall fun g => ?_)
  have h1 : ‖⟪v, ρ g v⟫_ℂ‖ ≤ ‖v‖ * ‖v‖ := (norm_inner_le_norm _ _).trans (by rw [hρ.norm])
  rw [Real.norm_of_nonneg (by positivity), norm_star, sq]
  exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

theorem inner_toLp {f g : Γ → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, star (f x) * g x ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [RCLike.inner_apply, mul_comm]

theorem orthonormal_coef {σ : Γ → (A →L[ℂ] A)} (hσ : IsU σ) {d : ℝ} (hd : IsFd ν σ d) {ι : Type*} {e : ι → A}
    (he : Orthonormal ℂ e) :
    Orthonormal ℂ fun p : ι × ι => ((√d : ℝ) : ℂ) • (memLp_coef hσ hd (e p.1) (e p.2)).toLp _ := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
  have hs : conj ((√d : ℝ) : ℂ) * ((√d : ℝ) : ℂ) = d := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hd.1.le]
  rw [orthonormal_iff_ite]
  rintro ⟨k, l⟩ ⟨k', l'⟩
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, hs, inner_toLp]
  have h := (hd.2 (e l') (e k') (e l) (e k)).2
  have h2 : ∫ x, star ⟪e k, σ x (e l)⟫_ℂ * ⟪e k', σ x (e l')⟫_ℂ ∂ν =
      ⟪e l, e l'⟫_ℂ * ⟪e k', e k⟫_ℂ / (d : ℂ) := by
    rw [← h]
    exact integral_congr_ae (.of_forall fun x => mul_comm _ _)
  simp only []
  rw [h2, orthonormal_iff_ite.1 he l l', orthonormal_iff_ite.1 he k' k]
  by_cases h1 : k = k' <;> by_cases h3 : l = l' <;> simp [h1, h3, hd0, eq_comm]

end SlopeTestRemainingChoices

theorem isHilbertSchmidt_coefOp : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ) (hσ : IsU σ), IsU ρ → IsFd ν σ d →
    ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    GroundTheory.Automorphic.IsHilbertSchmidt (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hd v hm
  set T := coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm with hT
  let e := GroundTheory.Automorphic.stdHilbertBasis ℂ A
  have hX := memLp_diag hρ v hm
  have hon := orthonormal_coef hσ hd e.orthonormal
  have hsum := Orthonormal.inner_products_summable (hX.toLp _) hon
  have hsd : √d ^ 2 = d := Real.sq_sqrt hd.1.le
  have key : ∀ p : _ × _, ‖⟪e p.1, T (e p.2)⟫_ℂ‖ ^ 2 =
      d⁻¹ * ‖⟪((√d : ℝ) : ℂ) • (memLp_coef hσ hd (e p.1) (e p.2)).toLp _, hX.toLp _⟫_ℂ‖ ^ 2 := by
    intro p
    have h1 : ⟪e p.1, T (e p.2)⟫_ℂ = ⟪hX.toLp _, (memLp_coef hσ hd (e p.1) (e p.2)).toLp _⟫_ℂ := by
      rw [hT, inner_coefOp, inner_toLp]
    rw [h1, inner_smul_left, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, hsd, norm_inner_symm, ← mul_assoc, inv_mul_cancel₀ hd.1.ne', one_mul]
  have hs2 : Summable fun p : _ × _ => ‖⟪e p.1, T (e p.2)⟫_ℂ‖ ^ 2 := by
    simp_rw [key]
    exact hsum.mul_left _
  rw [GroundTheory.Automorphic.isHilbertSchmidt_iff e]
  have h3 : ∑' l, ‖T (e l)‖ₑ ^ 2 = ∑' p : _ × _, ENNReal.ofReal (‖⟪e p.1, T (e p.2)⟫_ℂ‖ ^ 2) := by
    simp_rw [GroundTheory.Automorphic.enorm_sq_eq_tsum e (T _)]
    rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]
    refine tsum_congr fun p => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [h3]
  exact hs2.tsum_ofReal_lt_top

end GlobalTheory.CompanionTheory.RgHeA.CoefHS

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.CubeModels

theorem model_refine {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ) (ft : Algebra.FiniteType ℤ R₁)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π)
    (ρ : Y ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (h₁ : ρ ≫ pullback.fst _ _ = π)
    (h₂ : ρ ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom φ₁)) :
    IsModel φ₁ f (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ))) ρ := by
  obtain ⟨-, l, q, s, sq⟩ := hm
  have hc : Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom φ₁) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    subst e
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨ft, inferInstance, inferInstance, inferInstance, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (v₁₃ := f₀) (h₂₂ := Spec.map (CommRingCat.ofHom ψ)) ?_ h₂ (IsPullback.of_hasPullback _ _)
  rw [h₁, ← hc]
  exact sq

def refineMap {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π) :
    Y ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)) :=
  pullback.lift π (f ≫ Spec.map (CommRingCat.ofHom φ₁)) (by
    have hc : Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom φ₁) ≫ Spec.map (CommRingCat.ofHom ψ) := by
      subst e
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [Category.assoc, ← hc]
    exact hm.2.2.2.2.w)

theorem model_refine' {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ) (ft : Algebra.FiniteType ℤ R₁)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π) :
    IsModel φ₁ f (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ))) (refineMap e hm) :=
  model_refine e ft hm _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem hasModel_of_spreads : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) →
    GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → GlobalTheory.SpreadingModels.LBSpreads →
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f →
      ∀ M : LB Y, M.IsLB → GlobalTheory.SpreadingModels.HasModel f M := by
  intro hS hSm hPr hLB R _ Y f hsm hpr M hM
  obtain ⟨R₀, _, φ, Y₀, f₀, π, hm⟩ := hS R Y f inferInstance inferInstance inferInstance
  obtain ⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩ := hSm R R₀ φ Y Y₀ f f₀ π hm hsm
  have m₁ := model_refine' e₁ ft₁ hm
  obtain ⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩ := hPr R R₁ φ₁ Y _ f _ _ m₁ hpr
  have m₂ := model_refine' e₂ ft₂ m₁
  obtain ⟨R₃, _, ψ₃, φ₃, ρ, e₃, ft₃, r₁, r₂, M₃, hM₃, w, hw⟩ := hLB R R₂ φ₂ Y _ f _ _ m₂ M hM
  have m₃ := model_refine e₃ ft₃ m₂ ρ r₁ r₂
  have sm₁' : Smooth (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) := sm₁
  have pr₂' : IsProper (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := pr₂
  refine ⟨R₃, inferInstance, Algebra.FiniteType.isNoetherianRing ℤ R₃, φ₃, _,
    pullback.snd (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) (Spec.map (CommRingCat.ofHom ψ₃)), ρ,
    inferInstance, inferInstance, m₃.2.2.2.2, M₃, hM₃, w, hw⟩

end GlobalTheory.CompanionTheory.CubeModels
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntertwinerAdjoint
section
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA.TwPf

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {ρ : Γ → (A →L[ℂ] A)}

theorem inner_map_map (hU : IsU ρ) (g : Γ) (x y : A) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨_, _, hnorm, _⟩ := hU
  let L : A →ₗᵢ[ℂ] A := ⟨(ρ g : A →ₗ[ℂ] A), hnorm g⟩
  exact L.inner_map_map x y

theorem map_mul_apply (hU : IsU ρ) (g h : Γ) (x : A) : ρ (g * h) x = ρ g (ρ h x) := by
  obtain ⟨_, hmul, _, _⟩ := hU
  rw [hmul, ContinuousLinearMap.mul_apply]

theorem inner_translate (hU : IsU ρ) (a g b : Γ) (u : A) :
    ⟪ρ a u, ρ g (ρ b u)⟫_ℂ = ⟪u, ρ (a⁻¹ * g * b) u⟫_ℂ := by
  have h : ρ g (ρ b u) = ρ a (ρ (a⁻¹ * g * b) u) := by
    rw [← GlobalTheory.CompanionTheory.RgHeA.TwPf.map_mul_apply hU, ← GlobalTheory.CompanionTheory.RgHeA.TwPf.map_mul_apply hU, show a * (a⁻¹ * g * b) = g * b by group]
  rw [h, GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_map_map hU]

end Unitary

theorem coefOp_translate {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ) (hρ : IsU ρ) (w₀ : A) (v : B)
    (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν) (x y : Γ) :
    ⟪σ x w₀, coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm (σ y w₀)⟫_ℂ =
      star ⟪ρ x⁻¹ v, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc (ρ y⁻¹ v)⟫_ℂ := by
  rw [GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp]
  simp_rw [GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_translate hσ, GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_translate hρ, inv_inv]
  have key : ∀ F : Γ → ℂ, ∫ g, F (x⁻¹ * g * y) ∂ν = ∫ g, F g ∂ν := fun F =>
    (integral_mul_left_eq_self (fun h => F (h * y)) x⁻¹).trans (integral_mul_right_eq_self F y)
  have hstar : star (∫ g, star ⟪w₀, σ g w₀⟫_ℂ * ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ ∂ν) =
      ∫ g, ⟪w₀, σ g w₀⟫_ℂ * star ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ ∂ν := by
    have h := (integral_conj (μ := ν)
      (f := fun g => star ⟪w₀, σ g w₀⟫_ℂ * ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ)).symm
    simpa [map_mul] using h
  rw [hstar, ← key (fun g => ⟪w₀, σ g w₀⟫_ℂ * star ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [show x * (x⁻¹ * g * y) * y⁻¹ = g by group]
  exact mul_comm _ _

end GlobalTheory.CompanionTheory.RgHeA.TwPf
end
end

