module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.SubfieldChart


open Filter Topology in
theorem exists_finite_test {A : Type} {e : A → ℂ} {N : Set (A → ℂ)} (hN : N ∈ 𝓝 e) :
    ∃ (n : ℕ) (r : Fin n → A) (ε : ℝ), 0 < ε ∧ ∀ u : A → ℂ, (∀ i, ‖u (r i) - e (r i)‖ < ε) → u ∈ N := by
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, hI, t, ht, hsub⟩ := hN
  obtain ⟨n, r, hr⟩ := hI.fin_param
  have h1 : Set.pi Set.univ (fun i => t (r i)) ∈ 𝓝 (fun i => e (r i)) :=
    set_pi_mem_nhds Set.finite_univ fun i _ => ht (r i)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 h1
  refine ⟨n, r, ε, hε, fun u hu => hsub fun a ha => ?_⟩
  rw [← hr.2] at ha
  obtain ⟨i, rfl⟩ := ha
  refine hb (a := fun i => u (r i)) ?_ i trivial
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro j
  rw [dist_eq_norm]
  exact hu j

section Ring

variable {k A : Type} [Field k] [Algebra k ℂ] [CommRing A] [Algebra k A]

def extPt (x : A →ₐ[k] ℂ) : ℂ ⊗[k] A →ₐ[ℂ] ℂ :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) x fun _ _ => Commute.all _ _

def resPt (z : ℂ ⊗[k] A →ₐ[ℂ] ℂ) : A →ₐ[k] ℂ :=
  (z.restrictScalars k).comp Algebra.TensorProduct.includeRight

theorem extPt_tmul (x : A →ₐ[k] ℂ) (c : ℂ) (a : A) : extPt x (c ⊗ₜ a) = c * x a := by
  simp [extPt]

theorem resPt_apply (z : ℂ ⊗[k] A →ₐ[ℂ] ℂ) (a : A) : resPt z a = z (1 ⊗ₜ a) := rfl

theorem resPt_extPt (x : A →ₐ[k] ℂ) : resPt (extPt x) = x := by
  ext a
  rw [resPt_apply, extPt_tmul, _root_.one_mul]

theorem extPt_resPt (z : ℂ ⊗[k] A →ₐ[ℂ] ℂ) : extPt (resPt z) = z := by
  ext a
  simp [extPt_tmul, resPt_apply]

theorem exists_continuous_extPt (t : ℂ ⊗[k] A) :
    ∃ F : (A → ℂ) → ℂ, Continuous F ∧ ∀ x : A →ₐ[k] ℂ, F x = extPt x t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨fun _ => 0, continuous_const, fun x => by simp⟩
  | tmul c a => exact ⟨fun u => c * u a, by fun_prop, fun x => (extPt_tmul x c a).symm⟩
  | add s t hs ht =>
    obtain ⟨F, hF, hF'⟩ := hs
    obtain ⟨G, hG, hG'⟩ := ht
    exact ⟨fun u => F u + G u, hF.add hG, fun x => by simp [hF', hG']⟩

theorem exists_chart_algebra (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d k A]
    (e : A →ₐ[k] ℂ) :
    ∃ (W : Set (Fin d → ℂ)) (p : (Fin d → ℂ) → (A →ₐ[k] ℂ)) (n : ℕ) (r : Fin n → A) (ε : ℝ),
      IsOpen W ∧ 0 ∈ W ∧ p 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => p w a) W) ∧
      Set.InjOn p W ∧ ∀ x : A →ₐ[k] ℂ, (∀ i, ‖x (r i) - e (r i)‖ < ε) → ∃ w ∈ W, x = p w := by
  have hc : (algebraMap ℂ (ℂ ⊗[k] A)).IsStandardSmoothOfRelativeDimension d :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).2 inferInstance
  obtain ⟨φ, hφc, hφ, hφ0⟩ := HolChart.exists_etale_coords_vanishing _ hc (extPt e).toRingHom
    (fun a => (extPt e).commutes a)
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (ℂ ⊗[k] A) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) (ℂ ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin d) ℂ) (ℂ ⊗[k] A) := hφ
  obtain ⟨W, σ, n, f, ε, hW, hW0, hσ0, hε, hσd, hσt, hσs⟩ :=
    exists_holomorphic_section_of_etale d (ℂ ⊗[k] A) (extPt e) hφ0
  choose F hF hF' using fun j => exists_continuous_extPt (f j)
  have hN : {u : A → ℂ | ∀ j, ‖F j u - extPt e (f j)‖ < ε} ∈ nhds (e : A → ℂ) := by
    refine IsOpen.mem_nhds ?_ fun j => ?_
    · rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun j =>
        isOpen_lt (((hF j).sub continuous_const).norm) continuous_const
    · rw [hF', sub_self, norm_zero]; exact hε
  obtain ⟨m, r, δ, hδ, hr⟩ := exists_finite_test hN
  refine ⟨W, fun w => resPt (σ w), m, r, δ, hW, hW0, ?_, hδ, fun a => hσd (1 ⊗ₜ a), ?_, ?_⟩
  · show resPt (σ 0) = e
    rw [hσ0, resPt_extPt]
  · intro w hw w' hw' h
    have h1 : σ w = σ w' := by
      rw [← extPt_resPt (σ w), ← extPt_resPt (σ w')]
      exact congrArg extPt h
    funext i
    rw [← hσt w hw i, h1, hσt w' hw' i]
  · intro x hx
    obtain ⟨w, hw, h⟩ := hσs (extPt x) fun j => by
      rw [← hF']; exact hr x hx j
    exact ⟨w, hw, (resPt_extPt x).symm.trans (congrArg resPt h)⟩

end Ring

theorem exists_holomorphic_chart :
    ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (y₀ : Sp ℂ ⟶ X), SmoothOfRelativeDimension d s → y₀ ≫ s = spMap σ → ∃ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (U : X.Opens) (f : Fin d → Γ(X, U)) (n : ℕ) (r : Fin n → Γ(X, U)), IsOpen B ∧ (0 : Fin d → ℂ) ∈ B ∧ y 0 = y₀ ∧ (∀ b ∈ B, y b ≫ s = spMap σ) ∧ IsHolTo B y ∧ Set.InjOn y B ∧ ⊤ ≤ y₀ ⁻¹ᵁ U ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U → (∀ i, ‖valAt' x U (r i) - valAt' y₀ U (r i)‖ < ε) → x ∈ y '' B := by
  intro k _ σ X s d y₀ hX hy₀
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ :=
    hX.exists_isStandardSmoothOfRelativeDimension (y₀ (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : s (y₀ (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = s (y₀ (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [h2]; exact h1
  subst hU₀
  let c : k →+* Γ(X, U) :=
    (s.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hc : c.IsStandardSmoothOfRelativeDimension d :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (s.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv hsm
  let _ : Algebra k ℂ := σ.toAlgebra
  let _ : Algebra k Γ(X, U) := c.toAlgebra
  have _ : Algebra.IsStandardSmoothOfRelativeDimension d k Γ(X, U) := hc
  let pt : (Γ(X, U) →+* ℂ) → (Sp ℂ ⟶ X) := fun e =>
    Spec.map (CommRingCat.ofHom e : Γ(X, U) ⟶ CommRingCat.of ℂ) ≫ hU.fromSpec
  have hptU : ∀ e, ⊤ ≤ pt e ⁻¹ᵁ U := fun e p _ => hU.range_fromSpec.le ⟨_, rfl⟩
  have hptv : ∀ e f, valAt' (pt e) U f = e f := fun e f => by
    rw [valAt', dite_eq_left (hptU e)]
    exact congrArg (fun ψ => ψ.hom f)
      (AffinePointValues.appLE_specMap_fromSpec hU (CommRingCat.ofHom e) (hptU e))
  have hpts : ∀ e, pt e ≫ s = spMap (e.comp c) := fun e => by
    simp only [pt]
    rw [Category.assoc, AffinePointValues.fromSpec_comp hU s hle, ← Spec.map_comp]
    rfl
  have hsurj : ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U →
      ∃ e : Γ(X, U) →ₐ[k] ℂ, pt e.toRingHom = x := by
    intro x hxs hx
    let e : Γ(X, U) →+* ℂ := (x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom
    have he : pt e = x := AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x hx
    have h1 : spMap (e.comp c) = spMap σ := by rw [← hpts, he, hxs]
    have h2 : e.comp c = σ := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    exact ⟨{ e with commutes' := fun a => RingHom.congr_fun h2 a }, he⟩
  have hyU : ⊤ ≤ y₀ ⁻¹ᵁ U := ((valAt'_rules X y₀).1 U).2 hp
  obtain ⟨e, rfl⟩ := hsurj y₀ hy₀ hyU
  obtain ⟨W, p, n, r, ε, hW, hW0, hp0, hε, hpd, hpi, hps⟩ := exists_chart_algebra d e
  refine ⟨W, fun w => pt (p w).toRingHom, U, fun _ => 0, n, r, hW, hW0, by simp only [hp0],
    fun b _ => ?_, fun V f => ?_, fun w hw w' hw' h => hpi hw hw' ?_, hyU, ε, hε,
    fun x hxs hx hxe => ?_⟩
  · rw [hpts]
    congr 2
    exact RingHom.ext fun a => (p b).commutes a
  · exact HolChart.hol_of_affine valAt'_rules hU hW (fun w => pt (p w).toRingHom)
      (fun w _ => hptU _) (fun a => (hpd a).congr fun w _ => hptv _ a) V f
  · refine AlgHom.ext fun a => ?_
    have h1 := hptv (p w).toRingHom a
    have h' : pt (p w).toRingHom = pt (p w').toRingHom := h
    rw [h', hptv] at h1
    exact h1.symm
  · obtain ⟨e', rfl⟩ := hsurj x hxs hx
    obtain ⟨w, hw, h⟩ := hps e' fun i => by
      have := hxe i
      rw [hptv, hptv] at this
      exact this
    exact ⟨w, hw, by rw [h]⟩

end GlobalTheory.SubfieldChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.EtaleFamily

theorem analyticAt_eval₂Hom {E R J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CommRing R]
    (φ : E → (R →+* ℂ)) (u : E → J → ℂ) (w : E) (hφ : ∀ a, AnalyticAt ℂ (fun z => φ z a) w)
    (hu : ∀ i, AnalyticAt ℂ (fun z => u z i) w) (q : MvPolynomial J R) :
    AnalyticAt ℂ (fun z => MvPolynomial.eval₂Hom (φ z) (u z) q) w := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.eval₂Hom_C] using hφ a
  | add P Q hP hQ => simp only [map_add (f := _)]; exact hP.add hQ
  | mul_X P i hP =>
    simp only [map_mul, MvPolynomial.eval₂Hom_X']
    exact hP.mul (hu i)

theorem exists_local_inverse {E S J σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [CommRing S] [Fintype J] [Fintype σ] [DecidableEq σ]
    (χ : E → (S →+* ℂ)) (rel : σ → MvPolynomial J S) (c : σ → J) (hc : Function.Bijective c)
    (z₀ : E) (u₀ : J → ℂ) (hχ : ∀ a, AnalyticAt ℂ (fun z => χ z a) z₀)
    (hdet : (Matrix.of fun s r : σ =>
      MvPolynomial.eval₂Hom (χ z₀) u₀ (MvPolynomial.pderiv (c s) (rel r))).det ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph (E × (J → ℂ)) (E × (σ → ℂ)),
      (∀ w, Φ w = (w.1, fun r => MvPolynomial.eval₂Hom (χ w.1) w.2 (rel r))) ∧
      (z₀, u₀) ∈ Φ.source ∧ AnalyticOnNhd ℂ Φ.symm Φ.target := by
  first
  | exact @_root_.GlobalTheory.AnalyticLineDerivative.main
  | exact _root_.GlobalTheory.AnalyticLineDerivative.main
  | (apply _root_.GlobalTheory.AnalyticLineDerivative.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AnalyticLineDerivative.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AnalyticLineDerivative.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AnalyticLineDerivative.main ..)

theorem exists_holomorphic_sections :
    ∀ (m g : ℕ) (A R : Type) [CommRing A] [CommRing R] (ψ : MvPolynomial (Fin g) A →+* R) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (b₀ : Fin m → ℂ) (e : R →+* ℂ), ψ.Etale → IsOpen B → b₀ ∈ B → (∀ a, DifferentiableOn ℂ (fun b => φ b a) B) → (∀ a, e (ψ (MvPolynomial.C a)) = φ b₀ a) → ∃ (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (R →+* ℂ)) (n : ℕ) (f : Fin n → R) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))), IsOpen N ∧ IsOpen O ∧ (b₀, fun j => e (f j)) ∈ O ∧ (∀ a, DifferentiableOn ℂ (fun q => σ q a) N) ∧ (∀ q ∈ N, q.1 ∈ B ∧ (∀ a, σ q (ψ (MvPolynomial.C a)) = φ q.1 a) ∧ ∀ i, σ q (ψ (MvPolynomial.X i)) = q.2 i) ∧ ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) → (b, fun j => x (f j)) ∈ O → (b, fun i => x (ψ (MvPolynomial.X i))) ∈ N ∧ σ (b, fun i => x (ψ (MvPolynomial.X i))) = x := by
  intro m g A R _ _ ψ B φ b₀ e hψ hB hb₀ hφ he
  classical
  letI : Algebra (MvPolynomial (Fin g) A) R := ψ.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) A) R := hψ
  obtain ⟨J, τ, _, _, P, hP⟩ := (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1
    ‹Algebra.Etale (MvPolynomial (Fin g) A) R›).out
  letI := Fintype.ofFinite J
  letI := Fintype.ofFinite τ
  have hcard : Fintype.card τ = Fintype.card J := by
    have := P.card_relations_le_card_vars_of_isFinite
    simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] at this hP
    omega
  have hbij : Function.Bijective P.map :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨P.map_inj, hcard⟩
  let π : MvPolynomial J (MvPolynomial (Fin g) A) →+* R := MvPolynomial.eval₂Hom ψ P.val
  have hπeq : ∀ a, π a = MvPolynomial.aeval P.val a := fun a => rfl
  have hπ : Function.Surjective π := P.aeval_val_surjective
  let χ : (Fin m → ℂ) × (Fin g → ℂ) → (MvPolynomial (Fin g) A →+* ℂ) :=
    fun q => MvPolynomial.eval₂Hom (φ q.1) q.2
  have hχ : ∀ q : (Fin m → ℂ) × (Fin g → ℂ), q.1 ∈ B → ∀ a, AnalyticAt ℂ (fun z => χ z a) q := by
    intro q hq a
    refine analyticAt_eval₂Hom (fun z : (Fin m → ℂ) × (Fin g → ℂ) => φ z.1) (fun z => z.2) q
      (fun c => ?_) (fun i => ?_) a
    · exact AnalyticAt.comp (g := fun b => φ b c) (f := fun w : (Fin m → ℂ) × (Fin g → ℂ) => w.1)
        (GlobalTheory.SCV.analyticAt_of_differentiableOn (hφ c) (hB.mem_nhds hq)) analyticAt_fst
    · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) i).comp
        (ContinuousLinearMap.snd ℂ (Fin m → ℂ) (Fin g → ℂ))).analyticAt _
  have hevj : ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) →
      MvPolynomial.eval₂Hom (χ (b, fun i => x (ψ (MvPolynomial.X i)))) (fun i => x (P.val i))
        = x.comp π := by
    intro b x hx
    refine MvPolynomial.ringHom_ext' ?_ ?_
    · refine MvPolynomial.ringHom_ext ?_ ?_
      · intro a; simp [χ, π, hx]
      · intro a; simp [χ, π]
    · intro i; simp [π]
  have hker : ∀ a, π a = 0 ↔ a ∈ Ideal.span (Set.range P.relation) := by
    intro a
    rw [P.span_range_relation_eq_ker]
    rw [P.ker_eq_ker_aeval_val]
    rfl
  obtain ⟨Φ, hΦ, hpS, hsymm⟩ := exists_local_inverse χ P.relation P.map hbij
    (b₀, fun i => e (ψ (MvPolynomial.X i))) (fun i => e (P.val i)) (hχ _ hb₀) (by
      rw [hevj b₀ e he]
      have h1 := (P.jacobian_isUnit.map e).ne_zero
      rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply, ← hπeq] at h1
      have h2 := (e.comp π).map_det P.jacobiMatrix
      have h3 : (e.comp π).mapMatrix P.jacobiMatrix = Matrix.of fun s r : τ =>
          (e.comp π) (MvPolynomial.pderiv (P.map s) (P.relation r)) := by
        ext s r
        simp [P.jacobiMatrix_apply]
      rw [← h3, ← h2]
      exact h1)
  have hfst : ∀ q, (q, 0) ∈ Φ.target → (Φ.symm (q, 0)).1 = q := by
    intro q hq
    have := Φ.right_inv hq
    rw [hΦ] at this
    exact congrArg Prod.fst this
  have hex : ∀ q : (Fin m → ℂ) × (Fin g → ℂ), ∃ x : R →+* ℂ, (q, 0) ∈ Φ.target →
      x.comp π = MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2 := by
    intro q
    by_cases hq : (q, 0) ∈ Φ.target
    · have hle : RingHom.ker π ≤
          RingHom.ker (MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2) := by
        intro a ha
        have : Ideal.span (Set.range P.relation) ≤
            RingHom.ker (MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2) := by
          rw [Ideal.span_le]
          rintro _ ⟨r, rfl⟩
          have h1 := Φ.right_inv hq
          rw [hΦ, hfst q hq] at h1
          exact congrFun (congrArg Prod.snd h1) r
        exact this ((hker a).1 ha)
      exact ⟨π.liftOfSurjective hπ ⟨_, hle⟩, fun _ => RingHom.ext fun c =>
        RingHom.liftOfRightInverse_comp_apply π _ (Function.rightInverse_surjInv hπ) ⟨_, hle⟩ c⟩
    · exact ⟨e, fun h => absurd h hq⟩
  choose s hs using hex
  let eqv := (Fintype.equivFin (Fin g ⊕ J))
  let κ : (Fin m → ℂ) × (Fin (Fintype.card (Fin g ⊕ J)) → ℂ) →
      ((Fin m → ℂ) × (Fin g → ℂ)) × (J → ℂ) :=
    fun y => ((y.1, fun i => y.2 (eqv (Sum.inl i))), fun i => y.2 (eqv (Sum.inr i)))
  have hκ : Continuous κ := by fun_prop
  let f : Fin (Fintype.card (Fin g ⊕ J)) → R :=
    fun j => Sum.elim (fun i => ψ (MvPolynomial.X i)) P.val (eqv.symm j)
  have hκf : ∀ (b : Fin m → ℂ) (x : R →+* ℂ), κ (b, fun j => x (f j)) =
      ((b, fun i => x (ψ (MvPolynomial.X i))), fun i => x (P.val i)) := by
    intro b x
    simp [κ, f]
  have hNo : IsOpen {q : (Fin m → ℂ) × (Fin g → ℂ) | q.1 ∈ B ∧ (q, 0) ∈ Φ.target} :=
    (hB.preimage continuous_fst).inter
      (Φ.open_target.preimage (continuous_id.prodMk continuous_const))
  refine ⟨{q | q.1 ∈ B ∧ (q, 0) ∈ Φ.target}, s, _, f, {y | y.1 ∈ B ∧ κ y ∈ Φ.source}, hNo,
    (hB.preimage continuous_fst).inter (Φ.open_source.preimage hκ), ⟨hb₀, ?_⟩, ?_, ?_, ?_⟩
  · rw [hκf]; exact hpS
  · intro a
    obtain ⟨c, rfl⟩ := hπ a
    refine DifferentiableOn.congr
      (f := fun q => MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2 c) ?_ ?_
    · intro q hq
      refine (AnalyticAt.differentiableAt ?_).differentiableWithinAt
      have h1 : AnalyticAt ℂ (fun z : (Fin m → ℂ) × (Fin g → ℂ) => Φ.symm (z, 0)) q :=
        AnalyticAt.comp (f := fun z : (Fin m → ℂ) × (Fin g → ℂ) => (z, (0 : τ → ℂ)))
          (hsymm _ hq.2) (analyticAt_id.prod analyticAt_const)
      refine analyticAt_eval₂Hom χ (fun z => (Φ.symm (z, 0)).2) q (hχ q hq.1) (fun i => ?_) c
      exact AnalyticAt.comp (f := fun z : (Fin m → ℂ) × (Fin g → ℂ) => Φ.symm (z, 0))
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) i).comp
        (ContinuousLinearMap.snd ℂ ((Fin m → ℂ) × (Fin g → ℂ)) (J → ℂ))).analyticAt _) h1
    · intro q hq
      exact DFunLike.congr_fun (hs q hq.2) c
  · intro q hq
    refine ⟨hq.1, fun a => ?_, fun i => ?_⟩
    · simpa [π, χ] using DFunLike.congr_fun (hs q hq.2) (MvPolynomial.C (MvPolynomial.C a))
    · simpa [π, χ] using DFunLike.congr_fun (hs q hq.2) (MvPolynomial.C (MvPolynomial.X i))
  · rintro b x hx ⟨hb, hO⟩
    rw [hκf] at hO
    have hΦx : Φ ((b, fun i => x (ψ (MvPolynomial.X i))), fun i => x (P.val i)) =
        ((b, fun i => x (ψ (MvPolynomial.X i))), 0) := by
      rw [hΦ]
      refine Prod.ext rfl (funext fun r => ?_)
      change MvPolynomial.eval₂Hom (χ (b, fun i => x (ψ (MvPolynomial.X i))))
        (fun i => x (P.val i)) (P.relation r) = 0
      rw [hevj b x hx, RingHom.comp_apply, (hker _).2 (Ideal.subset_span ⟨r, rfl⟩), map_zero]
    have ht := Φ.map_source hO
    rw [hΦx] at ht
    refine ⟨⟨hb, ht⟩, ?_⟩
    have h1 := hs _ ht
    rw [← hΦx, Φ.left_inv hO, hevj b x hx] at h1
    ext a
    obtain ⟨c, rfl⟩ := hπ a
    exact DFunLike.congr_fun h1 c

end GlobalTheory.EtaleFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfLifting
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LatticeHom

theorem eq_zero_of_forall_smul_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Λ : Submodule ℤ E) (hd : DiscreteTopology Λ) {z : E} (hz : ∀ t : ℂ, t • z ∈ Λ) : z = 0 := by
  have hc : Continuous fun t : ℂ => (⟨t • z, hz t⟩ : Λ) := by fun_prop
  have h := (IsLocallyConstant.iff_continuous _).2 hc |>.apply_eq_of_preconnectedSpace 1 0
  simpa using congrArg Subtype.val h

theorem exists_linearEquiv_of_lifting {A : Over (Sp ℂ)} [GrpObj A] {L L₁ : LB A.left} {g : ℕ}
    (u : HolUnif A L g) (v : HolUnif A L₁ g)
    (hv : ∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)), (∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      IsOpen {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧
        DifferentiableOn ℂ (fun w => valAt' (a w).left U f)
          {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 →
      ∃ G : (Fin n → ℂ) → (Fin g → ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, v.ex (G w) = a w) :
    ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, v.ex (T z) = u.ex z := by
  obtain ⟨G, hG0, hGa, hGe⟩ := hv g u.ex (fun U f => by simpa using u.hol U f)
    ((u.ker 0).2 u.Λ.zero_mem)
  have hT := EndoLinear.fderiv_lifts v.ex v.ex_add v.Λ v.ker v.discrete u.ex u.ex_add G hG0
    hGa.differentiableAt hGe
  have hi : Function.Injective (fderiv ℂ G 0).toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    refine eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => ?_
    have hz' : fderiv ℂ G 0 z = 0 := hz
    rw [← u.ker, ← hT, map_smul, hz', smul_zero]
    exact (v.ker 0).2 v.Λ.zero_mem
  exact ⟨LinearEquiv.ofInjectiveEndo _ hi, hT⟩

theorem exists_linearEquiv_of_holUnif (hmul : Out.MulNSt) (P : Out.PolAV (Sp ℂ)) {L L' : LB P.A.left}
    (u : HolUnif P.A L P.g) (u' : HolUnif P.A L' P.g) :
    ∃ T : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u'.ex (T z) = u.ex z := by
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  obtain ⟨v, -, hv⟩ := @AbelianExp.exists_holUnif hmul hval (@holFamily_lift hval)
    (@isTopologicalGroup_complexPoints hval) (@PointsCompact.compactSpace_points_polAV hval hvalaff)
    (@HolChart.exists_holomorphic_chart hval hvalaff @exists_holomorphic_section_of_etale) P
  obtain ⟨T, hT⟩ := exists_linearEquiv_of_lifting u v hv
  obtain ⟨T', hT'⟩ := exists_linearEquiv_of_lifting u' v hv
  refine ⟨T.trans T'.symm, fun z => ?_⟩
  rw [← hT', ← hT]
  simp

end GlobalTheory.LatticeHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.ObjMaps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sab_id {S : Scheme.{0}} (t : SAB H S) : ∃ m : SABMap t t (𝟙 S), m.φ = 𝟙 _ :=
  ⟨ObjComp.sabMapId t, rfl⟩

theorem exists_sab_comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} (m : SABMap t' t f) (m' : SABMap t'' t' g) : ∃ n : SABMap t'' t (g ≫ f), n.φ = m'.φ ≫ m.φ :=
  sabComp pullCubComp E H S S' S'' t t' t'' f g m m'

theorem exists_sab_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} (m : SABMap t' t f) (n : SABMap t'' t (g ≫ f)) : ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ :=
  sabCancel pullCubCancel E H S S' S'' t t' t'' f g m n

end GlobalTheory.ObjMaps

namespace GlobalTheory

theorem ObjMaps.id_comp_cancel :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ o _ _ =>
    ⟨⟨ObjComp.objMapId o, rfl⟩, fun _ _ m => ⟨ObjComp.objMap_comp m, ObjComp.objMap_cancel m⟩⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientIsReducedIsNormalFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem quotient_isReduced_isNormal_flat :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsReduced X → IsReduced X') ∧ (IsLocallyNoetherian X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X') ∧ ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (s' : X' ⟶ Sp R), Flat (π ≫ s') → Flat s' := by
  rintro Γ _ _ X X' ρ π ⟨_, hπ, hV⟩
  have h : IsAffineQuotient ρ π :=
    ⟨hπ, ‹_›, fun W ↦ (hV W).1, fun W s hs ↦ (hV W).2 s fun g _ ↦ (hs g).2⟩
  refine ⟨fun _ ↦ h.isReduced, fun _ hN ↦ ?_, fun R _ _ s' _ ↦ ?_⟩
  · have := IsNormalScheme.of_pred hN
    have := h.isNormalScheme
    exact IsNormalScheme.pred X'
  · have := h.isSchemeTheoreticallyDominant
    exact flat_of_isSchemeTheoreticallyDominant
      (fun _ _ _ h ↦ IsDedekindDomain.flat_iff_torsion_eq_bot.mpr h) π s'

end GlobalTheory
end

