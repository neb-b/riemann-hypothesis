module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteGermProjectionOpenAt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem germ_eventually_zero_of_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {y : E}
    (hf : AnalyticAt ℂ f y) (hg : AnalyticAt ℂ g y) (hfg : ∀ᶠ z in 𝓝 y, f z * g z = 0) :
    (∀ᶠ z in 𝓝 y, f z = 0) ∨ (∀ᶠ z in 𝓝 y, g z = 0) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)
  by_cases hf0 : ∀ z ∈ Metric.ball y r, f z = 0
  · exact Or.inl (Filter.mem_of_superset (Metric.ball_mem_nhds y hr) hf0)
  · right
    push Not at hf0
    obtain ⟨p, hp, hfp⟩ := hf0
    have hgp : g =ᶠ[𝓝 p] 0 := by
      filter_upwards [(hball hp).1.1.continuousAt.eventually_ne hfp, Metric.isOpen_ball.mem_nhds hp]
        with z hz1 hz2
      exact (mul_eq_zero.1 (hball hz2).2).resolve_left hz1
    have hgan : AnalyticOnNhd ℂ g (Metric.ball y r) := fun z hz => (hball hz).1.2
    have hzero := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y r).isPreconnected hp hgp
    exact Filter.mem_of_superset (Metric.ball_mem_nhds y hr) fun z hz => by simpa using hzero hz

theorem germ_prod_eventually_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (h : ι → E → ℂ) {y : E} (s : Finset ι) (han : ∀ i ∈ s, AnalyticAt ℂ (h i) y)
    (hprod : ∀ᶠ z in 𝓝 y, ∏ i ∈ s, h i z = 0) : ∃ i ∈ s, ∀ᶠ z in 𝓝 y, h i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hprod.exists
    simp at hz
  | insert a s ha ih =>
    have hg : AnalyticAt ℂ (fun z => ∏ i ∈ s, h i z) y :=
      Finset.analyticAt_fun_prod s fun i hi => han i (Finset.mem_insert_of_mem hi)
    have hprod' : ∀ᶠ z in 𝓝 y, h a z * ∏ i ∈ s, h i z = 0 := by
      filter_upwards [hprod] with z hz
      rwa [Finset.prod_insert ha] at hz
    rcases germ_eventually_zero_of_mul (han a (Finset.mem_insert_self a s)) hg hprod' with h1 | h1
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨i, hi, h2⟩ := ih (fun i hi => han i (Finset.mem_insert_of_mem hi)) h1
      exact ⟨i, Finset.mem_insert_of_mem hi, h2⟩

theorem mem_of_projection_germ_injective {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {x : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hX : IsAnalyticNear X x)
    (hinj : ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
      ∀ᶠ y in 𝓝 (A x), h y = 0) : x ∈ X := by
  by_contra hx
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  have hne : ∃ i, f i x ≠ 0 := by
    by_contra hall
    push Not at hall
    have hmem : x ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hxN, hall⟩
    rw [← hXN] at hmem
    exact hx hmem.1
  obtain ⟨i, hi⟩ := hne
  have hev : ∀ᶠ z in 𝓝 x, z ∈ X → (fun _ : Fin d → ℂ => (1 : ℂ)) (A z) = 0 := by
    filter_upwards [(hf i x hxN).continuousAt.eventually_ne hi, hNo.mem_nhds hxN] with z hz1 hz2 hzX
    have hmem : z ∈ X ∩ N := ⟨hzX, hz2⟩
    rw [hXN] at hmem
    exact absurd (hmem.2 i) hz1
  obtain ⟨y, hy⟩ := (hinj (fun _ => 1) analyticAt_const hev).exists
  exact one_ne_zero hy

theorem FiniteGermProjectionOpenAt.proof (hcomp : AnalyticGermComponents.Statement)
    (hirr : IrreducibleFiniteGermProjectionOpenAt.Statement) : FiniteGermProjectionOpenAt.Statement := by
  classical
  intro σ _ X x d A hX hiso hinj V hV
  have hxX : x ∈ X := mem_of_projection_germ_injective A hX hinj
  obtain ⟨n, Y, hY, W, hW, hXW⟩ := hcomp σ X x hX hxX
  obtain ⟨W₀, hW₀, hisoW₀⟩ := hiso

  have hsome : ∃ i, ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) →
      (∀ᶠ z in 𝓝 x, z ∈ Y i → h (A z) = 0) → ∀ᶠ y in 𝓝 (A x), h y = 0 := by
    by_contra hnone
    push Not at hnone
    choose h han hvan hne using hnone
    have hprod : ∀ᶠ y in 𝓝 (A x), ∏ i ∈ Finset.univ, h i y = 0 := by
      have hpan : AnalyticAt ℂ (fun y => ∏ i ∈ Finset.univ, h i y) (A x) :=
        Finset.analyticAt_fun_prod Finset.univ fun i _ => han i
      refine hinj (fun y => ∏ i ∈ Finset.univ, h i y) hpan ?_
      filter_upwards [Filter.eventually_all.2 hvan, hW] with z hz hzW hzX
      have hmem : z ∈ (⋃ i, Y i) ∩ W := by
        rw [← hXW]
        exact ⟨hzX, hzW⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem.1
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hz i hi)
    obtain ⟨i, -, hi⟩ := germ_prod_eventually_zero h Finset.univ (fun i _ => han i) hprod
    exact hne i (hi.mono fun z hz => not_not.2 hz)
  obtain ⟨i, hi⟩ := hsome
  have hYX : Y i ∩ W ⊆ X := fun z hz => by
    have hmem : z ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.2 ⟨i, hz.1⟩, hz.2⟩
    rw [← hXW] at hmem
    exact hmem.1
  have hisoY : ∃ W' ∈ 𝓝 x, ∀ x' ∈ Y i ∩ W', A x' = A x → x' = x :=
    ⟨W ∩ W₀, Filter.inter_mem hW hW₀, fun x' hx' hAx' => hisoW₀ x' ⟨hYX ⟨hx'.1, hx'.2.1⟩, hx'.2.2⟩ hAx'⟩
  have himg := hirr σ (Y i) x d A (hY i).1 (hY i).2 hisoY hi (V ∩ W) (Filter.inter_mem hV hW)
  refine Filter.mem_of_superset himg (Set.image_mono ?_)
  rintro z ⟨hzY, hzV, hzW⟩
  exact ⟨hYX ⟨hzY, hzW⟩, hzV⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteModuloIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

def germCompRingHom {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    Germ (𝓝 (L x)) ℂ →+* Germ (𝓝 x) ℂ where
  toFun s := s.compTendsto L (L.continuous.tendsto x)
  map_one' := rfl
  map_mul' s t := Germ.inductionOn₂ s t fun _ _ => rfl
  map_zero' := rfl
  map_add' s t := Germ.inductionOn₂ s t fun _ _ => rfl

def holGermsPullback {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    holGerms (L x) →+* holGerms x :=
  ((germCompRingHom x L).comp (holGerms (L x)).subtype).codRestrict (holGerms x) fun s => by
    obtain ⟨b, hb, hbs⟩ := s.2
    refine ⟨b ∘ L, hb.comp (L.analyticAt x), ?_⟩
    show _ = germCompRingHom x L s.1
    rw [← hbs]
    rfl

theorem FiniteModuloIntegral.proof : FiniteModuloIntegral.Statement := by
  classical
  intro σ τ _ _ x k f L hf hfin g hg
  obtain ⟨n, e, he, hrep⟩ := hfin
  set φ := holGermsPullback x L with hφdef
  set I : Ideal (holGerms x) :=
    Ideal.span (Set.range fun i => (⟨f i, f i, hf i, rfl⟩ : holGerms x)) with hIdef
  let _ : Algebra (holGerms (L x)) (holGerms x ⧸ I) := ((Ideal.Quotient.mk I).comp φ).toAlgebra
  have hsmul : ∀ (s : holGerms (L x)) (q : holGerms x),
      s • Ideal.Quotient.mk I q = Ideal.Quotient.mk I (φ s * q) := by
    intro s q
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simp

  have hfg : Module.Finite (holGerms (L x)) (holGerms x ⧸ I) := by
    refine ⟨⟨Finset.univ.image fun m => Ideal.Quotient.mk I ⟨e m, e m, he m, rfl⟩, ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨⟨_, u, hu, rfl⟩, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨b, h, hb, hh, hev⟩ := hrep u hu
    have hq : Ideal.Quotient.mk I ⟨u, u, hu, rfl⟩ = ∑ m, (⟨b m, b m, hb m, rfl⟩ : holGerms (L x)) •
        Ideal.Quotient.mk I ⟨e m, e m, he m, rfl⟩ := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hsmul, ← map_sum]
      rw [Ideal.Quotient.eq]
      have hmem : ∑ i, (⟨h i, h i, hh i, rfl⟩ : holGerms x) * ⟨f i, f i, hf i, rfl⟩ ∈ I :=
        Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
      convert hmem using 1
      apply Subring.subtype_injective
      have e1 : (holGerms x).subtype ((⟨u, u, hu, rfl⟩ : holGerms x) -
          ∑ m, φ ⟨b m, b m, hb m, rfl⟩ * ⟨e m, e m, he m, rfl⟩) =
          Germ.coeRingHom (𝓝 x) (u - ∑ m, (b m ∘ L) * e m) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sub, map_sum, map_mul]
        rfl
      have e2 : (holGerms x).subtype (∑ i, (⟨h i, h i, hh i, rfl⟩ : holGerms x) * ⟨f i, f i, hf i, rfl⟩) =
          Germ.coeRingHom (𝓝 x) (∑ i, h i * f i) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul]
        rfl
      rw [e1, e2]
      refine Germ.coe_eq.2 ?_
      filter_upwards [hev] with z hz
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply, Function.comp_apply]
      rw [hz]
      ring
    rw [hq]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have := Algebra.IsIntegral.of_finite (holGerms (L x)) (holGerms x ⧸ I)

  obtain ⟨p, hpm, hp⟩ :=
    Algebra.IsIntegral.isIntegral (R := holGerms (L x)) (Ideal.Quotient.mk I ⟨g, g, hg, rfl⟩)
  rw [RingHom.algebraMap_toAlgebra, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem,
    hpm.as_sum] at hp
  simp only [eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C] at hp
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hp
  choose a ha hae using fun j : ℕ => (p.coeff j).2
  choose h hh hhe using fun i => (c i).2
  refine ⟨p.natDegree, fun j => a j, h, fun j => ha j, hh, ?_⟩
  have hcI : ∀ i, (holGerms x).subtype (c i) = Germ.coeRingHom (𝓝 x) (h i) := fun i => (hhe i).symm
  have hφI : ∀ j, (holGerms x).subtype (φ (p.coeff j)) = Germ.coeRingHom (𝓝 x) (a j ∘ L) := by
    intro j
    show germCompRingHom x L (p.coeff j).1 = _
    rw [← hae j]
    rfl
  have hgerm : Germ.coeRingHom (𝓝 x) (∑ i, h i * f i) = Germ.coeRingHom (𝓝 x)
      (g ^ p.natDegree + ∑ j ∈ Finset.range p.natDegree, (a j ∘ L) * g ^ j) := by
    have := congrArg (holGerms x).subtype hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_mul, map_pow, hcI, hφI] at this ⊢
    exact this
  filter_upwards [Germ.coe_eq.1 hgerm] with z hz
  simp only [Finset.sum_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_apply] at hz
  rw [Fin.sum_univ_eq_sum_range (fun j => a j (L z) * g z ^ j), hz]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionProperBall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem FiniteProjectionProperBall.proof : FiniteProjectionProperBall.Statement := by
  intro σ _ X w d A hX hiso U hU
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have hmem : N ∩ U ∩ W ∈ 𝓝 w := Filter.inter_mem (Filter.inter_mem (hNo.mem_nhds hwN) hU) hW
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hmem
  have hBN : Metric.closedBall w ρ ⊆ N := fun x hx => (hball hx).1.1

  set C : Set (σ → ℂ) := Metric.closedBall w ρ ∩ (fun z i => f i z) ⁻¹' {0} with hCdef
  have hCX : ∀ x ∈ C, x ∈ X := by
    intro x hx
    have hxN := hBN hx.1
    have : x ∈ X ∩ N := by
      rw [hXN]
      refine ⟨hxN, fun i => ?_⟩
      have := congrFun (show (fun i => f i x) = 0 from hx.2) i
      simpa using this
    exact this.1
  have hXC : ∀ x ∈ X, x ∈ Metric.closedBall w ρ → x ∈ C := by
    intro x hxX hxB
    have : x ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := hXN ▸ ⟨hxX, hBN hxB⟩
    refine ⟨hxB, ?_⟩
    show (fun i => f i x) = 0
    funext i
    simpa using this.2 i
  have hCcl : IsClosed C := by
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ Metric.isClosed_closedBall isClosed_singleton
    exact continuousOn_pi.mpr fun i => ((hf i).continuousOn).mono hBN
  have hC : IsCompact C := (isCompact_closedBall w ρ).of_isClosed_subset hCcl Set.inter_subset_left

  set S : Set (σ → ℂ) := C ∩ Metric.sphere w ρ with hSdef
  have hS : IsCompact S := hC.inter_right Metric.isClosed_sphere
  have hT : IsCompact (A '' S) := hS.image A.continuous
  have hAw : A w ∉ A '' S := by
    rintro ⟨x, hxS, hxA⟩
    have hxw : x = w := hWiso x ⟨hCX x hxS.1, (hball hxS.1.1).2⟩ hxA
    have hd := hxS.2
    rw [hxw, Metric.mem_sphere, dist_self] at hd
    exact hρ.ne hd
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.mp hT.isClosed.isOpen_compl (A w) hAw
  refine ⟨ρ, hρ, r, hr, fun x hx => (hball (Metric.ball_subset_closedBall hx)).1.2, ?_⟩
  intro K hKr hK
  have heq : {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K} = C ∩ A ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨⟨hxX, hxB⟩, hxK⟩
      exact ⟨hXC x hxX (Metric.ball_subset_closedBall hxB), hxK⟩
    · rintro ⟨hxC, hxK⟩
      refine ⟨⟨hCX x hxC, ?_⟩, hxK⟩
      have hle : dist x w ≤ ρ := hxC.1
      rcases hle.lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd ⟨x, ⟨hxC, heq⟩, rfl⟩ (hrT (hKr hxK))
  rw [heq]
  exact hC.inter_right (hK.isClosed.preimage A.continuous)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric

open MvPolynomial Matrix

noncomputable section

def entries {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : Fin a × Fin b → ℂ := fun ij => A ij.1 ij.2

def rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  bind₁ (fun ij : Fin d × Fin n => ∑ l, C (F (s ij.1) l) * X (l, ij.2)) p

theorem eval_rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) :
    eval (entries U) (rowsPoly F s p) = eval (entries ((F * U).submatrix s id)) p := by
  change eval₂Hom (RingHom.id ℂ) (entries U) (bind₁ _ p) = eval₂Hom (RingHom.id ℂ) _ p
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  simp [entries, Matrix.mul_apply]

theorem exists_rows_eq {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) (A : Matrix (Fin d) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, (F * U).submatrix s id = A := by
  refine ⟨star F * Matrix.of (Function.extend s (fun i => A i) 0), ?_⟩
  rw [← Matrix.mul_assoc, mem_unitaryGroup_iff.mp hF, Matrix.one_mul]
  ext i j
  simp [hs.extend_apply]

theorem rowsPoly_ne_zero {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) {p : MvPolynomial (Fin d × Fin n) ℂ}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : eval (entries A) p ≠ 0) : rowsPoly F s p ≠ 0 := by
  obtain ⟨U, hU⟩ := exists_rows_eq hF hs A
  intro h
  apply hA
  rw [← hU, ← eval_rowsPoly, h, map_zero]

theorem proof (hO : FiniteProjectionsContainOpen.Statement) (hU : UnitaryZariskiDense.Statement) :
    FiniteProjectionsGeneric.Statement := by
  classical
  intro n d J hJ hd
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hsub⟩ := hO n d J hJ hd
  have hA₀' := hA₀
  rw [hS] at hA₀'
  obtain ⟨p, hpS, hp⟩ := hA₀'
  have good : ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (entries A) p ≠ 0 → IsFiniteProjection J A :=
    fun A hA => hsub (by rw [hS]; exact ⟨p, hpS, hA⟩)
  have hdn : d ≤ n := by
    have h := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
    exact_mod_cast h
  refine ⟨⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hsub⟩, fun D hD hcl => ?_, fun m F => ?_⟩
  · obtain ⟨U, hUu, hUp⟩ := hU n (rowsPoly 1 (Fin.castLE hdn) p)
      (rowsPoly_ne_zero (one_mem _) (Fin.castLE_injective hdn) hp)
    have hUp' : eval (entries (U.submatrix (Fin.castLE hdn) id)) p ≠ 0 := by
      have := eval_rowsPoly 1 (Fin.castLE hdn) p U
      rw [Matrix.one_mul] at this
      exact this ▸ hUp
    have hAo : U.submatrix (Fin.castLE hdn) id ∈ orthoRows d n := by
      show _ * _ = _
      rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
        ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hUu,
        submatrix_one _ (Fin.castLE_injective hdn)]
    have hopen : IsOpen {B : Matrix (Fin d) (Fin n) ℂ | eval (entries B) p ≠ 0} :=
      isOpen_ne_fun ((MvPolynomial.continuous_eval p).comp
        (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)) continuous_const
    obtain ⟨B, hBp, hBD⟩ := mem_closure_iff.mp (hcl hAo) _ hopen hUp'
    exact ⟨B, hBD, good B hBp⟩
  · have hQ : (∏ ks : Fin m × (Fin d ↪ Fin n), rowsPoly (F ks.1 : Matrix (Fin n) (Fin n) ℂ) ks.2 p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun ks _ => rowsPoly_ne_zero (F ks.1).2 ks.2.injective hp
    obtain ⟨U, hUu, hUQ⟩ := hU n _ hQ
    refine ⟨U, hUu, fun k s => good _ ?_⟩
    rw [map_prod] at hUQ
    have := Finset.prod_ne_zero_iff.mp hUQ (k, s) (Finset.mem_univ _)
    change eval (entries U) (rowsPoly _ _ p) ≠ 0 at this
    rwa [eval_rowsPoly] at this

end

end GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFlatLocalRegularSequence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence Pointwise

def quotSMulTopQuotIdealSMulTopEquiv {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (I : Ideal B) (y : B) :
    QuotSMulTop y (M ⧸ (I • ⊤ : Submodule B M)) ≃ₗ[B]
      (QuotSMulTop y M ⧸ (I • ⊤ : Submodule B (QuotSMulTop y M))) :=
  (Submodule.quotEquivOfEq ((y • (⊤ : Submodule B M)).map (I • (⊤ : Submodule B M)).mkQ) (y • ⊤)
      (by rw [Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ])).symm ≪≫ₗ
    Submodule.quotientQuotientEquivQuotientSup (I • ⊤) (y • ⊤) ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (sup_comm _ _) ≪≫ₗ
    (Submodule.quotientQuotientEquivQuotientSup (y • ⊤) (I • ⊤)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ])

theorem FlatLocalRegularElement.iterate (h : FlatLocalRegularElement.Statement)
    {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B) (hl : IsLocalHom (algebraMap A B))
    (ys : List B) (hys : ∀ y ∈ ys, y ∈ maximalIdeal B)
    (M : Type) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (hfin : Module.Finite B M) (hflat : Module.Flat A M)
    (hreg : IsWeaklyRegular (M ⧸ ((maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B M))) ys) :
    IsWeaklyRegular M ys ∧ Module.Flat A (M ⧸ (Ideal.ofList ys • (⊤ : Submodule B M))) := by
  induction ys generalizing M with
  | nil =>
    refine ⟨IsWeaklyRegular.nil B M, ?_⟩
    have e : (M ⧸ (Ideal.ofList ([] : List B) • (⊤ : Submodule B M))) ≃ₗ[B] M :=
      Submodule.quotEquivOfEqBot _ (by rw [Ideal.ofList_nil, Submodule.bot_smul])
    exact Module.Flat.of_linearEquiv (e.restrictScalars A)
  | cons y ys ih =>
    rw [isWeaklyRegular_cons_iff] at hreg
    obtain ⟨hyM, hflat'⟩ := h A B hA hB hl M hfin hflat y (hys y List.mem_cons_self) hreg.1
    have hfin' : Module.Finite B (QuotSMulTop y M) := inferInstance
    obtain ⟨h1, h2⟩ := ih (fun z hz => hys z (List.mem_cons_of_mem _ hz)) (QuotSMulTop y M) hfin' hflat'
      (((quotSMulTopQuotIdealSMulTopEquiv _ y).isWeaklyRegular_congr ys).mp hreg.2)
    refine ⟨(isWeaklyRegular_cons_iff M y ys).mpr ⟨hyM, h1⟩, ?_⟩
    have : Module.Flat A (QuotSMulTop y M ⧸ (Ideal.ofList ys • (⊤ : Submodule B (QuotSMulTop y M)))) := h2
    exact Module.Flat.of_linearEquiv
      ((Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M y ys).restrictScalars A)

theorem FlatLocalRegularSequence.proof (h : FlatLocalRegularElement.Statement) :
    FlatLocalRegularSequence.Statement := by
  intro A B _ _ _ _ _ hA hB hl hflat rs ys hrs hreg hys hfib
  set I := (maximalIdeal A).map (algebraMap A B) with hI
  have hfib' : IsWeaklyRegular (B ⧸ (I • ⊤ : Submodule B B)) ys := by
    have e : (B ⧸ I) ≃ₗ[B] (B ⧸ (I • ⊤ : Submodule B B)) :=
      Submodule.quotEquivOfEq _ _ (by rw [Ideal.smul_eq_mul, Ideal.mul_top])
    rw [← Ideal.Quotient.algebraMap_eq, isWeaklyRegular_map_algebraMap_iff] at hfib
    exact (e.isWeaklyRegular_congr ys).mp hfib
  obtain ⟨hysB, hflatQ⟩ :=
    FlatLocalRegularElement.iterate h hA hB hl ys hys B inferInstance hflat hfib'
  have hrsN : IsWeaklyRegular (B ⧸ (Ideal.ofList ys • (⊤ : Submodule B B))) rs :=
    ((TensorProduct.lid A _).isWeaklyRegular_congr rs).mp (hreg.isWeaklyRegular_rTensor)
  have happ : IsWeaklyRegular B (ys ++ rs.map (algebraMap A B)) :=
    (isWeaklyRegular_append_iff B ys _).mpr
      ⟨hysB, (isWeaklyRegular_map_algebraMap_iff B _ rs).mpr hrsN⟩
  have : IsNoetherian B B := hB
  refine IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal happ List.perm_append_comm ?_
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hys r hr
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => (IsLocalRing.mem_maximalIdeal a).mp (hrs a ha) (isUnit_of_map_unit _ _ hu)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFibreRadicalAway
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem GenericFibreRadicalAway.proof (hR : GenericFibreRadical.Statement) :
    GenericFibreRadicalAway.Statement := by
  intro σ _ n K g hK
  obtain ⟨F, hF0, hF⟩ := hR σ (Option (Fin n)) (rabinowitschIdeal K g)
    ((isRadicalAway_iff_isRadical_rabinowitschIdeal K g).1 hK)
  refine ⟨F, hF0, fun t ht => ?_⟩
  have h := hF t ht
  rw [rabinowitschIdeal_map] at h
  exact (isRadicalAway_iff_isRadical_rabinowitschIdeal (fibreIdeal K t) _).2 h

end

end GroundTheory.Heights₂.Heights
end

