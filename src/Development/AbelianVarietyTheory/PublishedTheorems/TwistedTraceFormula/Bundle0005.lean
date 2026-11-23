module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0206

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison
section
noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.AdelicU (absFin absBar finEmb FvBar compFin compInf htFin htInf normFin)
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (infHt finHt finNorm finCoord)

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {ι : Type} [Fintype ι]
  (b : Module.Basis ι F E)

theorem absFin_le_coord (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) {K c : ℝ≥0}
    (hK : ∀ k, absFin F v ((1 : Fv F v) ⊗ₜ[F] b k) ≤ K)
    (hc : ∀ k, ‖(Algebra.TensorProduct.basis (Fv F v) b).repr y k‖₊ ≤ c) : absFin F v y ≤ K * c := by
  rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]
  refine GlobalTheory.AdelicU.absFin_sum_le F v _ _ fun k _ => ?_
  have e : ∀ a : Fv F v, a • (Algebra.TensorProduct.basis (Fv F v) b) k =
      ((1 : Fv F v) ⊗ₜ[F] b k) * (a ⊗ₜ[F] (1 : E)) := fun a => by
    simp [TensorProduct.smul_tmul']
  rw [e]
  refine (GlobalTheory.AdelicU.absFin_mul_le F v _ _).trans (mul_le_mul' (hK k) ?_)
  rw [GlobalTheory.AdelicU.absFin_tmul_one]
  exact hc k

theorem exists_trace_eq_repr : ∃ b' : ι → E, ∀ x k, Algebra.trace F E (b' k * x) = b.repr x k := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨fun k => ((Algebra.traceForm F E).toDual (traceForm_nondegenerate F E)).symm (b.coord k), fun x k => ?_⟩
  exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate F E) (b.coord k) x

theorem coord_le_absFin {b' : ι → E} (hb : ∀ x k, Algebra.trace F E (b' k * x) = b.repr x k)
    (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) (k : ι) :
    ‖(Algebra.TensorProduct.basis (Fv F v) b).repr y k‖₊ ≤ absFin F v ((1 : Fv F v) ⊗ₜ[F] b' k) * absFin F v y := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e : algebraMap (Fv F v) (FvBar F v) ((Algebra.TensorProduct.basis (Fv F v) b).repr y k) =
      ∑ τ : E →ₐ[F] FvBar F v, finEmb F v τ (((1 : Fv F v) ⊗ₜ[F] b' k) * y) := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy, mul_add, Finset.sum_add_distrib]
    | tmul a x =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, GlobalTheory.AdelicU.finEmb_tmul, ← Finset.mul_sum]
      rw [← trace_eq_sum_embeddings (FvBar F v), hb, Algebra.TensorProduct.basis_repr_tmul,
        IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v), ← map_mul]
      simp
  rw [← GlobalTheory.AdelicU.absBar_algebraMap, e]
  refine Valuation.map_sum_le (GlobalTheory.AdelicU.valBar F v) fun τ _ => ?_
  exact (GlobalTheory.AdelicU.le_absFin F v τ _).trans (GlobalTheory.AdelicU.absFin_mul_le F v _ _)

theorem exists_absFin_bound (x : ι → E) : ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧
    ∀ v, 1 ≤ K v ∧ ∀ k, absFin F v ((1 : Fv F v) ⊗ₜ[F] x k) ≤ K v := by
  refine ⟨fun v => max 1 (Finset.univ.sup fun k => absFin F v ((1 : Fv F v) ⊗ₜ[F] x k)), ?_, fun v =>
    ⟨le_max_left _ _, fun k => le_max_of_le_right
      (Finset.le_sup (f := fun k => absFin F v ((1 : Fv F v) ⊗ₜ[F] x k)) (Finset.mem_univ k))⟩⟩
  have h := eventually_all.2 fun k => GlobalTheory.AdelicU.eventually_absFin_le_one F ((1 : AF F) ⊗ₜ[F] x k)
  refine (eventually_cofinite.1 h).subset fun v hv hv' => hv (max_eq_left (Finset.sup_le fun k _ => ?_))
  simpa [compFin] using hv' k

theorem evalV_repr (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) (k : ι) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((Algebra.TensorProduct.basis (Af F) b).repr
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) k) =
      (Algebra.TensorProduct.basis (Fv F v) b).repr (compFin F E v z) k := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul a x => simp [compFin, GlobalTheory.AdelicU.evFin, Algebra.TensorProduct.basis_repr_tmul]

end Local

theorem finprod_le_mul {α : Type} {f g K : α → ℝ≥0} (hf : (Function.mulSupport f).Finite)
    (hg : (Function.mulSupport g).Finite) (hK : (Function.mulSupport K).Finite) (h : ∀ a, f a ≤ K a * g a) :
    ∏ᶠ a, f a ≤ (∏ᶠ a, K a) * ∏ᶠ a, g a := by
  rw [← finprod_mul_distrib hK hg]
  exact finprod_le_finprod' hf ((hK.union hg).subset (Function.mulSupport_mul _ _)) h

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (V : HSp D)

theorem evalV_finCoord (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) (i j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v (finCoord D (finMat D.sp.cm.sig V.gram g i j) k) =
      (Algebra.TensorProduct.basis (Fv D.host.F v) (Module.finBasis D.host.F D.host.E)).repr
        (compFin D.host.F D.host.E v ((Formalism.L2.Theta.matHom V g).1 i j)) k :=
  evalV_repr (Module.finBasis D.host.F D.host.E) v ((Formalism.L2.Theta.matHom V g).1 i j) k

theorem finNorm_le_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {g : GA D V} {c : ℝ≥0} : finNorm V v g ≤ c ↔
    ∀ i j k, ‖(Algebra.TensorProduct.basis (Fv D.host.F v) (Module.finBasis D.host.F D.host.E)).repr
      (compFin D.host.F D.host.E v ((Formalism.L2.Theta.matHom V g).1 i j)) k‖₊ ≤ c := by
  simp only [finNorm, Finset.sup_le_iff, Finset.mem_univ, true_imp_iff, Prod.forall, evalV_finCoord]

theorem exists_finNorm_comparison : ∃ K : HeightOneSpectrum (𝓞 D.host.F) → ℝ≥0, (Function.mulSupport K).Finite ∧
    ∀ v, 1 ≤ K v ∧ ∀ g : GA D V,
      finNorm V v g ≤ K v * normFin D.host.F v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)).1 ∧
      normFin D.host.F v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)).1 ≤ K v * finNorm V v g := by
  obtain ⟨b', hb⟩ := exists_trace_eq_repr (Module.finBasis D.host.F D.host.E)
  obtain ⟨K, hK, h⟩ := exists_absFin_bound (F := D.host.F) (Sum.elim (Module.finBasis D.host.F D.host.E) b')
  refine ⟨K, hK, fun v => ⟨(h v).1, fun g => ⟨(finNorm_le_iff V).2 fun i j k => ?_,
    (GlobalTheory.AdelicU.normFin_le_iff _ v).2 fun i j => ?_⟩⟩⟩
  · exact (coord_le_absFin _ hb v _ _).trans (mul_le_mul' ((h v).2 (.inr _))
      (GlobalTheory.AdelicU.absFin_le_normFin _ v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)).1 i j))
  · exact absFin_le_coord (Module.finBasis D.host.F D.host.E) v
      (compFin D.host.F D.host.E v ((Formalism.L2.Theta.matHom V g).1 i j)) (fun k => (h v).2 (.inl k))
      ((finNorm_le_iff V).1 le_rfl i j)

theorem height_comparison (hθ : IsInfFam θ) : ∃ C : ℝ, 0 < C ∧ ∀ g : GA D V,
    (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ≤ C * height V g ∧ height V g ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := by
  obtain ⟨K, hK, h⟩ := exists_finNorm_comparison V
  have key : ∀ {k a a' c c' : ℝ≥0}, 1 ≤ k → a ≤ k * c → a' ≤ k * c' → max 1 (max a a') ≤ k * max 1 (max c c') :=
    fun hk h1 h2 => max_le (one_le_mul_of_one_le_of_one_le hk (le_max_left _ _)) (max_le
      (h1.trans (mul_le_mul_right (le_max_of_le_right (le_max_left _ _)) _))
      (h2.trans (mul_le_mul_right (le_max_of_le_right (le_max_right _ _)) _)))
  have h1 : (1 : ℝ≥0) ≤ ∏ᶠ v, K v := one_le_finprod' fun v => (h v).1
  refine ⟨(∏ᶠ v, K v : ℝ≥0), by exact_mod_cast zero_lt_one.trans_le h1, fun g => ?_⟩
  have e : ∏ w, htInf D.host.F w (bc (compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom V g)) = ∏ τ, infHt θ V τ g :=
    (Function.Bijective.prod_comp (GlobalTheory.CMTypePlaces.places_bijective D) _).symm.trans
      (Finset.prod_congr rfl fun τ _ => htInf_eq_infHt V hθ τ g)
  have hi := fun v => (h v).2 g⁻¹
  simp only [map_inv] at hi
  have f1 := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite V g
  have f2 := GlobalTheory.AdelicU.finite_mulSupport_htFin D.host.F (Formalism.L2.Theta.matHom V g)
  have a1 := finprod_le_mul f1 f2 hK fun v => key (h v).1 ((h v).2 g).1 (hi v).1
  have a2 := finprod_le_mul f2 f1 hK fun v => key (h v).1 ((h v).2 g).2 (hi v).2
  unfold height GlobalTheory.AdelicU.heightGL GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height
  rw [e]
  constructor
  · exact_mod_cast (mul_le_mul_right a1 _).trans_eq (mul_left_comm _ _ _)
  · exact_mod_cast (mul_le_mul_right a2 _).trans_eq (mul_left_comm _ _ _)

end GlobalTheory.Grow

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
section
noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Host (HChar)
open GlobalTheory.LFun GlobalTheory.HeckeOne
open GlobalTheory.CMVal (eulerFactor IsHeckeL)

namespace GlobalTheory.Published

def HeckeLPartialContinuation : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K))), T.Finite →
    (∀ χ : HChar K, χ.IsUnitary → (¬ ∃ t : ℝ, IsNormPow χ t) →
      ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∀ s : ℂ, 1 < s.re → Λ s = heckeL T χ s) ∧ ∀ s : ℂ, 1 ≤ s.re → Λ s ≠ 0) ∧
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * zetaOff T s) ∧
      ∀ s : ℂ, 1 ≤ s.re → Z s ≠ 0

end GlobalTheory.Published

namespace GlobalTheory.HeckePartial

variable {K : Type} [Field K] [NumberField K]

def removed (T : Finset (HeightOneSpectrum (𝓞 K))) (χ : HChar K) (s : ℂ) : ℂ :=
  ∏ w ∈ T, eulerPoly (heckeFam χ w) (npow w (-s))

theorem differentiable_removed (T : Finset (HeightOneSpectrum (𝓞 K))) (χ : HChar K) :
    Differentiable ℂ (removed T χ) :=
  Differentiable.fun_finsetProd fun _ _ => differentiable_eulerPoly _ _

theorem eulerPoly_heckeFam_ne_zero {χ : HChar K} (hu : χ.IsUnitary) (w : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : 0 < s.re) : eulerPoly (heckeFam χ w) (npow w (-s)) ≠ 0 :=
  eulerPoly_ne_zero fun _ hb => ((bounded_heckeFam ∅ hu).norm_le le_rfl (Set.notMem_empty w) hb).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm w) (by linarith))

theorem removed_ne_zero (T : Finset (HeightOneSpectrum (𝓞 K))) {χ : HChar K} (hu : χ.IsUnitary) {s : ℂ}
    (hs : 0 < s.re) : removed T χ s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ => eulerPoly_heckeFam_ne_zero hu w hs

theorem heckeL_eq_mul_removed (T : Finset (HeightOneSpectrum (𝓞 K))) {χ : HChar K} (hu : χ.IsUnitary) {s a : ℂ}
    (hs : 1 < s.re) (ha : HasProd (eulerFactor χ s) a) : heckeL (T : Set _) χ s = a * removed T χ s := by
  have h1 := (converges_heckeFam (T : Set _) hu hs).hasProd
  have h2 : HasProd (fun w => locL (heckeFam χ) w s) _ :=
    HasProd.mul_compl (s := (T : Set _)) (Finset.hasProd T fun w => locL (heckeFam χ) w s) h1
  have h3 : a = (∏ w ∈ T, locL (heckeFam χ) w s) * heckeL (T : Set _) χ s := by
    refine ha.unique ?_
    exact (funext (fun w => locL_heckeFam χ w s) : (fun w => locL (heckeFam χ) w s) = eulerFactor χ s) ▸ h2
  have h4 : (∏ w ∈ T, locL (heckeFam χ) w s) = (removed T χ s)⁻¹ := by
    rw [removed, ← Finset.prod_inv_distrib]; rfl
  have h5 := removed_ne_zero T hu (s := s) (by linarith)
  rw [h3, h4]
  field_simp

theorem eq_one_add_of_re {s : ℂ} (hs : s.re = 1) : s = 1 + (s.im : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im s, hs]
  simp

theorem IsHeckeL.ne_zero_of_one_le {χ : HChar K} (hu : χ.IsUnitary) (hχ : ¬ ∃ t : ℝ, IsNormPow χ t) {Λ : ℂ → ℂ}
    (hΛ : IsHeckeL χ Λ) {s : ℂ} (hs : 1 ≤ s.re) : Λ s ≠ 0 := by
  rcases hs.lt_or_eq with hs | hs
  · rw [(hΛ.2 s hs).unique (hasProd_exp hu hs)]
    exact Complex.exp_ne_zero _
  · set t := s.im
    have hχ' : ¬ ∃ u : ℝ, IsNormPow (χ * normChar K t) u := fun ⟨u, h⟩ => hχ ⟨u + -t, by
      rw [isNormPow_iff] at h ⊢
      rw [normChar_add, ← h, mul_assoc, ← normChar_add, add_neg_cancel, normChar_zero, mul_one]⟩
    obtain ⟨Λ', h1, h2⟩ := exists_entire_ne_zero GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds
      (hu.mul (isUnitary_normChar t)) hχ'
    have h3 : IsHeckeL (χ * normChar K t) fun z => Λ (z + (t : ℂ) * Complex.I) :=
      ⟨hΛ.1.comp (by fun_prop), fun z hz => by
        rw [eulerFactor_mul_normChar]
        exact hΛ.2 _ (by simpa using hz)⟩
    have h4 := (isContAtOne_of_isHeckeL h3).apply_one_eq (isContAtOne_of_isHeckeL h1)
    rw [eq_one_add_of_re hs.symm]
    exact fun h => h2 (h4.symm.trans h)

theorem _root_.GlobalTheory.Published.HeckeLPartialContinuation_holds : GlobalTheory.Published.HeckeLPartialContinuation := by
  intro K _ _ T hT
  obtain ⟨T, rfl⟩ : ∃ T' : Finset _, (T' : Set _) = T := ⟨hT.toFinset, hT.coe_toFinset⟩
  refine ⟨fun χ hu hχ => ?_, ?_⟩
  · obtain ⟨Λ, hΛ⟩ := entire_of_not_normPow hu hχ
    exact ⟨fun s => Λ s * removed T χ s, hΛ.1.mul (differentiable_removed T χ),
      fun s hs => (heckeL_eq_mul_removed T hu hs (hΛ.2 s hs)).symm,
      fun s hs => mul_ne_zero (IsHeckeL.ne_zero_of_one_le hu hχ hΛ hs) (removed_ne_zero T hu (by linarith))⟩
  · obtain ⟨Z, hZd, hZ1, hZ⟩ := GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero K
    have hu : (1 : HChar K).IsUnitary := fun _ => by simp
    have hc : ∀ P : HeightOneSpectrum (𝓞 K), cf (1 : HChar K) P = 1 := fun P => if_pos fun _ _ => rfl
    refine ⟨fun s => Z s * removed T 1 s, hZd.mul (differentiable_removed T 1), fun s hs => ?_,
      fun s hs => mul_ne_zero ?_ (removed_ne_zero T hu (by linarith))⟩
    · have h := hasProd_exp hu hs
      simp only [hc] at h
      beta_reduce
      rw [← heckeL_one, heckeL_eq_mul_removed T hu hs h, hZ s hs, mul_assoc]
    · rcases hs.lt_or_eq with hs | hs
      · rw [hZ s hs]
        exact mul_ne_zero (sub_ne_zero.2 fun h => by rw [h] at hs; simp at hs) (Complex.exp_ne_zero _)
      · rw [eq_one_add_of_re hs.symm]
        by_cases ht : s.im = 0
        · simpa [ht] using hZ1
        · exact GlobalTheory.zetaEulerProduct_ne_zero_one_add_mul_I _ _ two_le_N sumN nonemptyN Z hZd hZ _ ht

end GlobalTheory.HeckePartial

end
end

