module

public import Mathlib
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0042
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.HermitianLattices.StatementLat
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BideterminantFunctionsOfShape
section
noncomputable section

namespace GlobalTheory.Mem.CanonicalSurjection

open MvPolynomial

def bideterminantFunctionsOfShape (K : Type) [CommRing K] (N : ℕ) (ν : Fin N → ℕ) : Set (Matrix (Fin N) (Fin N) K → K) :=
  {g | ∃ (Kc : ℕ) (sz : Fin Kc → ℕ) (hsz : ∀ k, sz k ≤ N) (I : ∀ k, Fin (sz k) → Fin N),
    Formalism.GradedWeylDivisibility.shapeDeg sz = ν ∧ (∀ k, StrictMono (I k)) ∧
      g = fun Y => eval (fun v : Fin N × Fin N => Y v.1 v.2) (Formalism.GradedWeylDivisibility.bideterminant K sz hsz I)}

end GlobalTheory.Mem.CanonicalSurjection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAevalEqSmulOnEigenspace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_pow_frob_commute {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {h : IsPlaceOver A w} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) :
    ∃ m : ℕ, 0 < m ∧ ∀ σ, Commute (ρ (frob (h := h)) ^ m) (ρ σ) := by
  have h1 : ∀ τ : Weil h, ∃ m : ℕ, 0 < m ∧ Commute (ρ (frob (h := h)) ^ m) (ρ τ) := by
    intro τ
    obtain ⟨m, hm, he⟩ := exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ (frob (h := h))
      (τ * frob (h := h) * τ⁻¹) (by simp [deg_mul, deg_inv])
    refine ⟨m, hm, ?_⟩
    rw [← map_pow, ← map_pow, conj_pow] at he
    show _ * _ = _ * _
    rw [← map_pow]
    conv_lhs => rw [he]
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  have h2 : ∀ S : Set (End ℂ V), S.Finite → (∀ x ∈ S, ∃ τ, ρ τ = x) →
      ∃ m : ℕ, 0 < m ∧ ∀ x ∈ S, Commute (ρ (frob (h := h)) ^ m) x := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨1, one_pos, by simp⟩
    | @insert x S _ _ ih =>
      intro hx
      obtain ⟨m, hm, hc⟩ := ih fun y hy => hx y (Set.mem_insert_of_mem _ hy)
      obtain ⟨τ, rfl⟩ := hx x (Set.mem_insert _ _)
      obtain ⟨n, hn, hc'⟩ := h1 τ
      refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
      rintro y (rfl | hy)
      · rw [mul_comm, pow_mul]; exact hc'.pow_left m
      · rw [pow_mul]; exact (hc y hy).pow_left n
  obtain ⟨m, hm, hc⟩ := h2 _ hρ.finite_range (by rintro _ ⟨σ, rfl⟩; exact ⟨_, rfl⟩)
  refine ⟨m, hm, fun σ => ?_⟩
  have h0 : deg ((frob (h := h) ^ deg σ)⁻¹ * σ) = 0 := by
    simp [deg_mul, deg_inv, deg_zpow, deg_frob]
  have h3 : Commute (ρ (frob (h := h)) ^ m) (ρ ((frob (h := h) ^ deg σ)⁻¹ * σ)) :=
    hc _ ⟨⟨_, deg_eq_zero_iff.mp h0⟩, rfl⟩
  have h4 : Commute (ρ (frob (h := h)) ^ m) (ρ (frob (h := h) ^ deg σ)) :=
    (((Commute.refl (frob (h := h))).zpow_right _).map ρ).pow_left m
  have := h4.mul_right h3
  rwa [← map_mul, mul_inv_cancel_left] at this

open NumberField IsDedekindDomain Polynomial Module in
private lemma exists_polynomial_eigenspace_smul_lemma {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (f : ℂ → ℂ) :
    ∃ p : ℂ[X], ∀ (α : ℂ) (v : V), v ∈ T.eigenspace α → aeval T p v = f α • v := by
  classical
  have hfin : Set.Finite {μ | T.HasEigenvalue μ} := Module.End.finite_hasEigenvalue T
  refine ⟨Lagrange.interpolate hfin.toFinset id f, fun α v hv => ?_⟩
  by_cases hv0 : v = 0
  · simp [hv0]
  have hev : T.HasEigenvector α v := ⟨hv, hv0⟩
  rw [Module.End.aeval_apply_of_hasEigenvector hev]
  have hnode := Lagrange.eval_interpolate_at_node (s := hfin.toFinset) (v := id) f
    (Set.injOn_id _) (i := α) (by simpa using Module.End.hasEigenvalue_of_hasEigenvector hev)
  simp only [id] at hnode
  rw [hnode]

open NumberField IsDedekindDomain Polynomial Module in
private lemma eq_of_eq_on_eigenspaces_lemma_2 {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (hT : T.IsSemisimple) {g g' : Module.End ℂ V}
    (h : ∀ (α : ℂ) (v : V), v ∈ T.eigenspace α → g v = g' v) : g = g' := by
  have hle : ⨆ α, T.eigenspace α ≤ LinearMap.ker (g - g') :=
    iSup_le fun α v hv => by simp [sub_eq_zero, h α v hv]
  rw [hT.iSup_eigenspace_eq_top] at hle
  ext v
  simpa [sub_eq_zero] using hle (Submodule.mem_top : v ∈ ⊤)

open NumberField IsDedekindDomain Polynomial Module in
private lemma mem_eigenspace_pow_lemma_3 {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) {α : ℂ} {v : V} (hv : v ∈ T.eigenspace α) (m : ℕ) :
    v ∈ (T ^ m).eigenspace (α ^ m) := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

open NumberField IsDedekindDomain Polynomial Module in
private lemma commute_aeval_of_commute_lemma_4 {V : Type} [AddCommGroup V] [Module ℂ V]
    {S T : Module.End ℂ V} (hST : Commute S T) (p : ℂ[X]) : Commute S (aeval T p) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add (f := _)]; exact hp.add_right hr
  | monomial n x => rw [aeval_monomial]; exact (Algebra.commute_algebraMap_right x S).mul_right (hST.pow_right n)


open NumberField IsDedekindDomain Polynomial Module in
theorem _root_.GlobalTheory.WeilDeligne.WDRep.iso_of_N_eq_smul : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a b : _root_.GlobalTheory.WeilDeligne.WDRep h V) (c : ℂ), c ≠ 0 → a.ρ = b.ρ →
    b.N = c • a.N → a.Iso b := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a b c hc hρ hN
  classical
  set φ := _root_.GlobalTheory.WeilDeligne.frob (h := h) with hφ
  set Φ : Module.End ℂ V := a.ρ φ with hΦdef
  have hΦ : Φ.IsSemisimple := a.semisimple φ
  have hq : (1 : ℝ) < (_root_.Formalism.ConjugateSelfDual.normV w : ℝ) := by exact_mod_cast _root_.GlobalTheory.WeilDeligne.one_lt_normV w
  set s : ℂ := Complex.log c / (Real.log (_root_.Formalism.ConjugateSelfDual.normV w : ℝ) : ℂ) with hsdef
  have hlogq : (Real.log (_root_.Formalism.ConjugateSelfDual.normV w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hq).ne'
  have hs : Complex.exp (s * Real.log (_root_.Formalism.ConjugateSelfDual.normV w : ℝ)) = c := by
    rw [hsdef, div_mul_cancel₀ _ hlogq, Complex.exp_log hc]
  set lam : ℂ → ℂ := fun α => Complex.exp (s * Real.log ‖α‖) with hlamdef
  have hlam : ∀ α : ℂ, α ≠ 0 → lam ((_root_.Formalism.ConjugateSelfDual.normV w : ℂ) * α) = c * lam α := by
    intro α hα
    simp only [hlamdef, norm_mul, Complex.norm_natCast]
    rw [Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hα)]
    rw [Complex.ofReal_add, mul_add, Complex.exp_add, hs]
  have hΦinj : ∀ v : V, Φ v = 0 → v = 0 := by
    intro v hv
    have : a.ρ φ⁻¹ (Φ v) = v := by
      rw [hΦdef, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← this, hv, map_zero]
  obtain ⟨p, hp⟩ := exists_polynomial_eigenspace_smul_lemma Φ lam
  obtain ⟨p', hp'⟩ := exists_polynomial_eigenspace_smul_lemma Φ (fun α => (lam α)⁻¹)
  have hgg' : aeval Φ p * aeval Φ p' = 1 := eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
    rw [Module.End.mul_apply, hp' α v hv, map_smul, hp α v hv, smul_smul,
      inv_mul_cancel₀ (Complex.exp_ne_zero _), one_smul, Module.End.one_apply]
  have hg'g : aeval Φ p' * aeval Φ p = 1 := eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
    rw [Module.End.mul_apply, hp α v hv, map_smul, hp' α v hv, smul_smul,
      mul_inv_cancel₀ (Complex.exp_ne_zero _), one_smul, Module.End.one_apply]
  refine ⟨LinearEquiv.ofLinear (aeval Φ p) (aeval Φ p') hgg' hg'g, ?_, ?_⟩
  · intro σ v
    rw [← hρ]
    change aeval Φ p (a.ρ σ v) = a.ρ σ (aeval Φ p v)
    obtain ⟨m, hm, hpow⟩ := _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq E Ω A w h V a.ρ
      a.smooth (σ * φ * σ⁻¹) φ
      (by rw [_root_.GlobalTheory.WeilDeligne.deg_mul, _root_.GlobalTheory.WeilDeligne.deg_mul, _root_.GlobalTheory.WeilDeligne.deg_inv]; ring)
    rw [← map_pow, conj_pow, map_mul, map_mul, map_pow] at hpow
    have hcomm : Commute (a.ρ σ) (Φ ^ m) := by
      calc a.ρ σ * Φ ^ m = a.ρ σ * Φ ^ m * (a.ρ σ⁻¹ * a.ρ σ) := by
            rw [← map_mul, inv_mul_cancel, map_one, mul_one]
        _ = Φ ^ m * a.ρ σ := by rw [← mul_assoc, hpow]
    obtain ⟨pm, hpm⟩ := exists_polynomial_eigenspace_smul_lemma (Φ ^ m)
      (fun μ => Complex.exp (s * Real.log ‖μ‖ / m))
    have hgm : aeval Φ p = aeval (Φ ^ m) pm := eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
      rw [hp α v hv, hpm (α ^ m) v (mem_eigenspace_pow_lemma_3 Φ hv m)]
      congr 1
      simp only [hlamdef, norm_pow, Real.log_pow]
      congr 1
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    rw [hgm]
    exact (LinearMap.congr_fun (commute_aeval_of_commute_lemma_4 hcomm pm) v).symm
  · intro v
    rw [hN]
    change aeval Φ p (a.N v) =
      c • a.N (aeval Φ p v)
    have key : aeval Φ p * a.N =
        c • (a.N * aeval Φ p) :=
      eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
        rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply, hp α v hv, map_smul]
        by_cases hα : α = 0
        · have hv0 : v = 0 := hΦinj v (by
            rw [Module.End.mem_eigenspace_iff] at hv
            rw [hv, hα, zero_smul])
          simp [hv0]
        · rw [hp _ _ (a.map_N_eigenspace
            (_root_.GlobalTheory.WeilDeligne.deg_frob) hv), hlam α hα, smul_smul]
    exact LinearMap.congr_fun key v

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertiaStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_restrictScalars_pow_mod_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w → IsPlaceOver A v ∧ normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 E) ∧ (∀ ι ∈ Ine (F := K) A, ι.restrictScalars E ∈ Ine (F := E) A) ∧ ∀ (σ : G K Ω) (φ : G E Ω), IsFrob A (normV w) σ → IsFrob A (normV v) φ → σ.restrictScalars E * (φ ^ w.asIdeal.inertiaDeg (𝓞 E))⁻¹ ∈ Ine (F := E) A := by
  first | exact @GlobalTheory.FrobRestrict.frob_restrict | exact GlobalTheory.FrobRestrict.frob_restrict | (intros; apply GlobalTheory.FrobRestrict.frob_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDualLatticeBaseChange
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.DualBC

variable {K : Type} [Field K] [NumberField K] [StarRing K]


omit [NumberField K] in
theorem mem_dual_iff {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (A : Submodule (𝓞 K) (Fin d → K)) (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A ↔
      ∀ y ∈ A, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Formalism.DivisionValues.hform H y x := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]


omit [NumberField K] in
theorem hform_eq {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (x y : Fin d → K) :
    Formalism.DivisionValues.hform H x y = ∑ j, star (x j) * (H.mulVec y) j := by
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul]
  ring


omit [NumberField K] in
theorem star_int (c : 𝓞 K) : algebraMap (𝓞 K) K (Formalism.DivisionValues.cO K c) = star (algebraMap (𝓞 K) K c) := rfl


omit [StarRing K] in
theorem exists_extend {d : ℕ} (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsFullLattice K A)
    (f : A →ₗ[𝓞 K] 𝓞 K) :
    ∃ F : (Fin d → K) →ₗ[K] K, ∀ x : A, F x = algebraMap (𝓞 K) K (f x) := by
  classical
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨s, hs, b, hb, hsA⟩ := Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 K) A hA.span_eq_top
  obtain ⟨c, hc0, hc⟩ := Formalism.HermitianLatticesTheory.dualLattice_denom (R := 𝓞 K) b A hA.fg
  have hbA : ∀ i, b i ∈ A := fun i => by rw [hb i]; exact hsA i.2
  let F : (Fin d → K) →ₗ[K] K := b.constr K (fun i => algebraMap (𝓞 K) K (f ⟨b i, hbA i⟩))
  let F' : A →ₗ[𝓞 K] K := (F.restrictScalars (𝓞 K)).comp A.subtype
  let g' : A →ₗ[𝓞 K] K := (Algebra.linearMap (𝓞 K) K).comp f
  let P : Submodule (𝓞 K) (Fin d → K) := (LinearMap.eqLocus F' g').map A.subtype
  have hspan : Submodule.span (𝓞 K) (Set.range b) ≤ P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨b i, hbA i⟩, ?_, rfl⟩
    show F (b i) = algebraMap (𝓞 K) K (f ⟨b i, hbA i⟩)
    exact b.constr_basis K _ i
  refine ⟨F, fun x => ?_⟩
  obtain ⟨z, hz, hzx⟩ := hspan (hc x x.2)
  have hz' : z = c • x := Subtype.ext (by simpa using hzx)
  have hzF : F' z = g' z := hz
  rw [hz', map_smul, map_smul] at hzF
  simp only [F', g', LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply,
    Algebra.linearMap_apply, Algebra.smul_def] at hzF
  exact mul_left_cancel₀ (by simpa using hc0) hzF

theorem exists_family {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (hH : IsUnit H.det)
    (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsFullLattice K A) :
    ∃ (n : ℕ) (a b : Fin n → Fin d → K), (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A) ∧
      ∀ y, y = ∑ i, Formalism.DivisionValues.hform H (a i) y • b i := by
  classical
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨n, g, f, hgf⟩ := Formalism.HermitianLatticesTheory.finitely_generated_projective_coords (K := K) A hA.fg hinj
  choose F hF using fun i => exists_extend A hA (f i)
  let w : Fin n → Fin d → K := fun i => H⁻¹.mulVec (fun j => star (F i (Pi.single j 1)))
  have hFcoord : ∀ i (y : Fin d → K), F i y = ∑ j, y j * F i (Pi.single j 1) := by
    intro i y
    conv_lhs => rw [← Finset.univ_sum_single y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Pi.single j (y j) : Fin d → K) = y j • Pi.single j 1 by
      ext k; by_cases hk : k = j <;> simp [hk], map_smul, smul_eq_mul]
  have hw : ∀ i (y : Fin d → K), Formalism.DivisionValues.hform H y (w i) = star (F i y) := by
    intro i y
    rw [hform_eq, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec, hFcoord,
      star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
  have hexp : ∀ y : Fin d → K, y = ∑ i, F i y • (g i : Fin d → K) := by
    have hT : (∑ i, (F i).smulRight (g i : Fin d → K)) = LinearMap.id := by
      refine LinearMap.ext_on hA.span_eq_top fun x hx => ?_
      have h1 := congrArg (fun v : A => (v : Fin d → K)) (hgf ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      conv_rhs => rw [h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hF i ⟨x, hx⟩, algebraMap_smul]
    intro y
    have := LinearMap.congr_fun hT y
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply] at this
    exact this.symm
  have hnd : ∀ z : Fin d → K, (∀ u, Formalism.DivisionValues.hform H u z = 0) → z = 0 := by
    intro z hz
    have hHz : H.mulVec z = 0 := by
      ext i
      have := hz (Pi.single i 1)
      rw [hform_eq, Finset.sum_eq_single i (fun j _ hj => by simp [hj])
        (by simp)] at this
      simpa using this
    rw [← Matrix.one_mulVec z, ← Matrix.nonsing_inv_mul _ hH, ← Matrix.mulVec_mulVec, hHz,
      Matrix.mulVec_zero]
  refine ⟨n, fun i => (g i : Fin d → K), w, fun i => (g i).2, fun i => ?_, fun y => ?_⟩
  · rw [mem_dual_iff]
    intro y hy
    refine ⟨Formalism.DivisionValues.cO K (f i ⟨y, hy⟩), ?_⟩
    rw [star_int, hw, hF i ⟨y, hy⟩]
  · refine (sub_eq_zero.1 (hnd _ fun u => ?_)).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, sub_eq_zero, map_sum]
    conv_rhs => rw [hexp u]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, hw, smul_eq_mul, smul_eq_mul,
      starRingEnd_apply, mul_comm]

theorem dual_baseChange : ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K'] (φ : K →+* K') (d d' : ℕ)
  (G : Matrix (Fin d') (Fin d) K'), Function.Bijective G.mulVec → ∀ (H : Matrix (Fin d) (Fin d) K) (H' : Matrix (Fin d') (Fin d') K'),
  (∀ x y : Fin d → K, Formalism.DivisionValues.hform H' (Matrix.mulVec G fun k => φ (x k)) (Matrix.mulVec G fun k => φ (y k)) = φ (Formalism.DivisionValues.hform H x y)) →
  IsUnit H.det → ∀ A : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K A →
    Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H')
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K)))) =
    Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) ''
      ((Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A : Submodule (𝓞 K) (Fin d → K)) : Set (Fin d → K))) := by
  intro K K' _ _ _ _ _ _ φ d d' G hG H H' hHH' hH A hA
  classical
  set ι : (Fin d → K) → (Fin d' → K') := fun x => Matrix.mulVec G fun k => φ (x k) with hι
  have ι_add : ∀ x y, ι (x + y) = ι x + ι y := by
    intro x y
    simp only [hι, Pi.add_apply, map_add (f := _)]
    rw [← Matrix.mulVec_add]
    rfl
  have ι_smul : ∀ (c : K) x, ι (c • x) = φ c • ι x := by
    intro c x
    simp only [hι, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← Matrix.mulVec_smul]
    rfl
  have ι_sum : ∀ {m : ℕ} (v : Fin m → Fin d → K), ι (∑ i, v i) = ∑ i, ι (v i) := by
    intro m v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hι, Finset.sum_apply, map_sum]
    rw [← Matrix.mulVec_sum]
    congr 1
    ext k
    simp [Finset.sum_apply]
  have ι_single : ∀ k : Fin d, ι (Pi.single k 1) = G.mulVec (Pi.single k 1) := by
    intro k
    simp only [hι]
    congr 1
    ext j
    by_cases hj : j = k <;> simp [hj]
  have hspanι : Submodule.span K' (Set.range ι) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨v, rfl⟩ := hG.2 z
    rw [← Finset.univ_sum_single v, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [show (Pi.single k (v k) : Fin d → K') = v k • Pi.single k 1 by
      ext j; by_cases hj : j = k <;> simp [hj], Matrix.mulVec_smul, ← ι_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hιH : ∀ x y, Formalism.DivisionValues.hform H' (ι x) (ι y) = φ (Formalism.DivisionValues.hform H x y) := hHH'
  apply le_antisymm
  · intro x hx
    obtain ⟨n, a, b, ha, hb, hab⟩ := exists_family H hH A hA
    have hT : (∑ i, (Formalism.DivisionValues.hform H' (ι (a i))).smulRight (ι (b i))) = LinearMap.id := by
      refine LinearMap.ext_on hspanι ?_
      rintro _ ⟨y, rfl⟩
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
        hιH]
      conv_rhs => rw [hab y]
      rw [ι_sum]
      simp only [ι_smul]
    have hx' : x = ∑ i, Formalism.DivisionValues.hform H' (ι (a i)) x • ι (b i) := by
      have := LinearMap.congr_fun hT x
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply,
        LinearMap.id_apply] at this
      exact this.symm
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := (mem_dual_iff H' _ x).1 hx (ι (a i))
      (Submodule.subset_span ⟨a i, ha i, rfl⟩)
    rw [← hc, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, hb i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_dual_iff]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      obtain ⟨c, hc⟩ := (mem_dual_iff H A z).1 hz y hy
      refine ⟨RingOfIntegers.mapRingHom φ c, ?_⟩
      rw [hιH, ← hc]
      rfl
    | zero => exact ⟨0, by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨c₁, hc₁⟩ := h₁
      obtain ⟨c₂, hc₂⟩ := h₂
      exact ⟨c₁ + c₂, by rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, hc₁, hc₂]⟩
    | smul r y _ h =>
      obtain ⟨c, hc⟩ := h
      refine ⟨Formalism.DivisionValues.cO K' r * c, ?_⟩
      rw [← algebraMap_smul K' r y, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, hc,
        star_int, starRingEnd_apply]

end GlobalTheory.Mem.DualBC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemSpanLowerWeightsOfBorelEigenvector
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem mulVec_mem_sle_of_isBEig : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam → ∀ B : GL (Fin n) ℂ, Φ B *ᵥ v ∈ Sle Φ lam := by
  intro n ι _ _ Φ hΦ v lam hv B
  have hdom : DomLE lam lam := ⟨rfl, fun _ => le_rfl⟩
  have hvS : v ∈ Sle Φ lam := by
    refine Submodule.subset_span ⟨lam, hdom, fun D hD => hv.2 D ?_⟩
    intro a b hab
    exact hD (ne_of_gt hab)

  have hstab : ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual →
      ∀ w ∈ Sle Φ lam, Φ L *ᵥ w ∈ Sle Φ lam := by
    refine _root_.GlobalTheory.lowerTriangular_GL_induction _ ?_ ?_ ?_ ?_
    · intro w hw; rw [hΦ.one, one_mulVec]; exact hw
    · intro A C hA hC w hw
      rw [hΦ.mul, ← mulVec_mulVec]
      exact hA _ (hC w hw)
    · intro D hD w hw
      refine Submodule.span_induction (p := fun w _ => Φ D *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        rw [hu D hD]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ν, hν, hu⟩)
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx
    · intro i j s T hji hT w hw
      refine Submodule.span_induction (p := fun w _ => Φ T *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        exact _root_.GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle Φ hΦ lam ν hν u hu i j hji s T hT
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx

  have hbig : ∀ C : GL (Fin n) ℂ,
      (∀ (k : ℕ) (hk : k ≤ n), (C.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) →
      Φ C *ᵥ v ∈ Sle Φ lam := by
    intro C hC
    obtain ⟨L, U, hL, hU, rfl⟩ := _root_.GlobalTheory.LUDecomp.lu C hC
    rw [hΦ.mul, ← mulVec_mulVec, hv.2 U hU, mulVec_smul]
    exact Submodule.smul_mem _ _ (hstab L hL v hvS)

  refine _root_.GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift Φ hΦ _ v B _ (_root_.GlobalTheory.shift_minors_vanish_finite B.val) ?_
  intro s hs C hC
  apply hbig
  rw [hC]
  simpa using hs

end GlobalTheory.AlgWtHW
end

