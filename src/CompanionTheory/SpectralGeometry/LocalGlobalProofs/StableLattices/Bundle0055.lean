module

public import Mathlib
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SchurOnMinimalSubspace
section
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.Factor

theorem schur_on_minimal_subspace :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (N : Set (H →L[ℂ] H))
    (Q : Submodule ℂ H), (∀ T ∈ N, star T ∈ N) → IsClosed (Q : Set H) → (∀ T ∈ N, ∀ v ∈ Q, T v ∈ Q) →
    (∀ U : Submodule ℂ H, IsClosed (U : Set H) → U ≤ Q → (∀ T ∈ N, ∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = Q) →
    ∀ A : H →L[ℂ] H, (∀ T ∈ N, T * A = A * T) → ∃ c : ℂ, ∀ v ∈ Q, A v - c • v ∈ Qᗮ := by
  intro H _ _ _ N Q hstar hQc hQinv hmin A hcomm
  haveI : CompleteSpace Q := hQc.completeSpace_coe

  let σ : N → (Q →L[ℂ] Q) := fun T =>
    (T.1.comp Q.subtypeL).codRestrict Q (fun v => hQinv T.1 T.2 v v.2)
  have hσ : ∀ (T : N) (v : Q), ((σ T v : Q) : H) = T.1 v := fun _ _ => rfl

  have hperp : ∀ T ∈ N, ∀ w ∈ Qᗮ, T w ∈ Qᗮ := by
    intro T hT w hw
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro u hu
    have h1 : ⟪u, T w⟫_ℂ = ⟪(star T) u, w⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [h1]
    exact hw _ (hQinv _ (hstar T hT) u hu)

  have hproj : ∀ T ∈ N, ∀ w : H, Q.starProjection (T w) = T (Q.starProjection w) := by
    intro T hT w
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · exact hQinv T hT _ (Submodule.starProjection_apply_mem Q w)
    · rw [← map_sub]
      exact hperp T hT _ (Submodule.sub_starProjection_mem_orthogonal w)
  let B : Q →L[ℂ] Q := (Q.orthogonalProjection).comp (A.comp Q.subtypeL)
  have hB : ∀ v : Q, ((B v : Q) : H) = Q.starProjection (A v) := fun _ => rfl
  obtain ⟨c, hc⟩ := GlobalTheory.hilbert_schur_of_adjoint_closed N Q σ
    (by
      intro g
      refine ⟨⟨star g.1, hstar g.1 g.2⟩, ?_⟩
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      change ⟪(star g.1) (x : H), (y : H)⟫_ℂ = ⟪(x : H), g.1 (y : H)⟫_ℂ
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left])
    (by
      intro S hS hSinv
      have hclosed : IsClosed ((S.map Q.subtype : Submodule ℂ H) : Set H) := by
        exact hQc.isClosedEmbedding_subtypeVal.isClosedMap _ hS
      have hle : S.map Q.subtype ≤ Q := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hinv : ∀ T ∈ N, ∀ v ∈ S.map Q.subtype, T v ∈ S.map Q.subtype := by
        rintro T hT _ ⟨x, hx, rfl⟩
        exact ⟨σ ⟨T, hT⟩ x, hSinv ⟨T, hT⟩ x hx, rfl⟩
      rcases hmin _ hclosed hle hinv with h | h
      · left
        rw [eq_bot_iff]
        intro x hx
        have hx' : (x : H) ∈ S.map Q.subtype := ⟨x, hx, rfl⟩
        rw [h, Submodule.mem_bot] at hx'
        exact (Submodule.mem_bot ℂ).2 (Subtype.ext hx')
      · right
        rw [eq_top_iff]
        intro x _
        have hx : (x : H) ∈ S.map Q.subtype := by
          rw [h]
          exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        have : y = x := Subtype.ext hyx
        exact this ▸ hy)
    B
    (by
      intro g
      ext v
      change Q.starProjection (A (g.1 v)) = g.1 (Q.starProjection (A v))
      have h := congrArg (fun X : H →L[ℂ] H => X (v : H)) (hcomm g.1 g.2)
      have h' : g.1 (A v) = A (g.1 v) := h
      rw [← h', hproj g.1 g.2])
  refine ⟨c, fun v hv => ?_⟩
  have h1 : Q.starProjection (A v) = c • v := by
    have := hB ⟨v, hv⟩
    rw [hc] at this
    simpa using this.symm
  rw [← h1]
  exact Submodule.sub_starProjection_mem_orthogonal _

end GlobalTheory.CompanionTheory.Factor
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SeparatedMovingStatement
section
open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

variable {G G' : Type} [Group G] [Group G']

def cosetEquiv (e : G ≃* G') (K : Subgroup G) : G ⧸ K ≃ G' ⧸ K.map e.toMonoidHom :=
  Quotient.congr (ra := QuotientGroup.leftRel K) (rb := QuotientGroup.leftRel (K.map e.toMonoidHom))
    e.toEquiv (by
      intro a b
      have h : (e.toEquiv a)⁻¹ * e.toEquiv b = e.toMonoidHom (a⁻¹ * b) := by simp
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, h]
      exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm)

lemma cosetEquiv_smul (e : G ≃* G') (K : Subgroup G) (g : G) (x : G ⧸ K) :
    cosetEquiv e K (g • x) = e g • cosetEquiv e K x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    change ((e (g * a) : G') : G' ⧸ K.map e.toMonoidHom) = ((e g * e a : G') : G' ⧸ K.map e.toMonoidHom)
    rw [map_mul]

theorem stSepMove : StSepMove := by
  intro G G' _ _ e K hK S
  classical
  let φ := cosetEquiv e K
  obtain ⟨Γ', hfin, hstab, hsep⟩ := hK (S.image φ)
  let Γ : Subgroup G := Γ'.comap e.toMonoidHom
  have hmem : ∀ γ : Γ, e (γ : G) ∈ Γ' := fun γ => γ.2
  have hsymm : ∀ γ' : Γ', e.symm (γ' : G') ∈ Γ := fun γ' => by
    change e (e.symm (γ' : G')) ∈ Γ'
    simpa using γ'.2
  have hact : ∀ (γ : Γ) (x : G ⧸ K), φ (γ • x) = (⟨e (γ : G), hmem γ⟩ : Γ') • φ x := fun γ x =>
    cosetEquiv_smul e K (γ : G) x
  refine ⟨Γ, ?_, ?_, ?_⟩
  · let f : MulAction.orbitRel.Quotient Γ' (G' ⧸ K.map e.toMonoidHom) →
        MulAction.orbitRel.Quotient Γ (G ⧸ K) :=
      Quotient.map' φ.symm (by
        rintro a b ⟨γ', rfl⟩
        refine ⟨⟨e.symm (γ' : G'), hsymm γ'⟩, ?_⟩
        apply φ.injective
        change φ (_ • φ.symm b) = φ (φ.symm (γ' • b))
        rw [hact]
        have h : (⟨e (e.symm (γ' : G')), hmem ⟨e.symm (γ' : G'), hsymm γ'⟩⟩ : Γ') = γ' :=
          Subtype.ext (e.apply_symm_apply _)
        rw [h, φ.apply_symm_apply, φ.apply_symm_apply])
    refine Finite.of_surjective f ?_
    intro q
    induction q using Quotient.inductionOn' with
    | h x =>
      exact ⟨Quotient.mk'' (φ x),
        congrArg (Quotient.mk'' (s₁ := MulAction.orbitRel Γ (G ⧸ K))) (φ.symm_apply_apply x)⟩
  · intro x
    let f : MulAction.stabilizer Γ x → MulAction.stabilizer Γ' (φ x) := fun γ =>
      ⟨⟨e ((γ : Γ) : G), hmem γ⟩, by
        rw [MulAction.mem_stabilizer_iff, ← hact, MulAction.mem_stabilizer_iff.mp γ.2]⟩
    refine Finite.of_injective f ?_
    intro a b hab
    have h := congrArg (fun c : MulAction.stabilizer Γ' (φ x) => ((c : Γ') : G')) hab
    exact Subtype.ext (Subtype.ext (e.injective h))
  · intro x hx y hy γ hxy
    apply φ.injective
    exact hsep (φ x) (Finset.mem_image_of_mem φ hx) (φ y) (Finset.mem_image_of_mem φ hy)
      ⟨e (γ : G), hmem γ⟩ (by rw [← hact, hxy])

end GlobalTheory.CompanionTheory.RgFl
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardPolynomialVanishesOnBicommutant
section
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Factor

open CompanionTheory.D.gk.admitted.FinOfPIAux

variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Diag

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem diag_mem_of_bicomm (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (C : Submodule ℂ (PiLp 2 (fun _ : ι => H))) (hcl : IsClosed (C : Set (PiLp 2 (fun _ : ι => H))))
    (hC : ∀ g, ∀ z ∈ C, diag (σ g) z ∈ C) (T : H →L[ℂ] H)
    (hT : ∀ S : H →L[ℂ] H, (∀ g, S * σ g = σ g * S) → S * T = T * S)
    (z : PiLp 2 (fun _ : ι => H)) (hz : z ∈ C) :
    diag T z ∈ C := by
  haveI : CompleteSpace C := hcl.completeSpace_coe
  have hPg := proj_comm (ι := ι) σ hσ C hC
  let Q : ι → ι → H →L[ℂ] H := fun k l =>
    (PiLp.proj 2 (fun _ : ι => H) k).comp (C.starProjection.comp (incl l))
  have hQ : ∀ k l, Q k l * T = T * Q k l := by
    intro k l
    apply hT
    intro g
    ext v
    simp only [Q, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    rw [← diag_incl, hPg, diag_apply]
  have hsum : ∀ w : PiLp 2 (fun _ : ι => H), ∀ k,
      (C.starProjection w).ofLp k = ∑ l, Q k l (w.ofLp l) := by
    intro w k
    conv_lhs => rw [← sum_incl w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Q, map_sum]
  have key : C.starProjection (diag T z) = diag T (C.starProjection z) := by
    ext k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, diag_apply, hsum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [diag_apply]
    exact congrArg (fun S : H →L[ℂ] H => S (z.ofLp l)) (hQ k l)
  have hz' : C.starProjection z = z := (Submodule.starProjection_eq_self_iff).2 hz
  rw [← hz', ← key]
  exact C.starProjection_apply_mem _

theorem sum_eq_zero_of_bicomm (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (L : ι → H →L[ℂ] H) (y : ι → H) (h : ∀ g, ∑ k, L k (σ g (y k)) = 0) (T : H →L[ℂ] H)
    (hT : ∀ S : H →L[ℂ] H, (∀ g, S * σ g = σ g * S) → S * T = T * S) :
    ∑ k, L k (T (y k)) = 0 := by
  let y' : PiLp 2 (fun _ : ι => H) := WithLp.toLp 2 y
  let V : Submodule ℂ (PiLp 2 (fun _ : ι => H)) :=
    Submodule.span ℂ (Set.range fun g : G => diag (σ g) y')
  have hdiag_mul : ∀ a b : G, ∀ w : PiLp 2 (fun _ : ι => H),
      diag (σ a) (diag (σ b) w) = diag (σ (a * b)) w := by
    intro a b w
    ext k
    simp only [diag_apply, map_mul, ContinuousLinearMap.mul_apply]
  have hCinv : ∀ g, ∀ z ∈ V.topologicalClosure, diag (σ g) z ∈ V.topologicalClosure := by
    intro g
    have hle : V ≤ V.topologicalClosure.comap
        ((diag (σ g) : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H))) :
          (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] (PiLp 2 (fun _ : ι => H))) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      show diag (σ g) (diag (σ b) y') ∈ V.topologicalClosure
      rw [hdiag_mul]
      exact V.le_topologicalClosure (Submodule.subset_span ⟨g * b, rfl⟩)
    have hcl' : IsClosed ((V.topologicalClosure.comap
        ((diag (σ g) : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H))) :
          (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] (PiLp 2 (fun _ : ι => H))) :
          Submodule ℂ (PiLp 2 (fun _ : ι => H))) : Set (PiLp 2 (fun _ : ι => H))) :=
      V.isClosed_topologicalClosure.preimage (diag (σ g)).continuous
    intro z hz
    exact Submodule.topologicalClosure_minimal V hle hcl' hz
  have hy' : y' ∈ V.topologicalClosure := by
    apply V.le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    ext k
    simp [diag_apply]
  have hT' := diag_mem_of_bicomm σ hσ V.topologicalClosure V.isClosed_topologicalClosure
    hCinv T hT y' hy'
  let Λ : (PiLp 2 (fun _ : ι => H)) →L[ℂ] H := ∑ k, (L k).comp (PiLp.proj 2 (fun _ : ι => H) k)
  have hΛ : ∀ w : PiLp 2 (fun _ : ι => H), Λ w = ∑ k, L k (w.ofLp k) := by
    intro w
    simp [Λ]
  have hker : V.topologicalClosure ≤ LinearMap.ker (Λ : (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] H) := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΛ, diag_apply]
      simpa [y'] using h g
    · exact Λ.isClosed_ker
  have hfin := hker hT'
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΛ, diag_apply] at hfin
  simpa [y'] using hfin

end Diag

theorem standard_polynomial_vanishes_on_bicommutant (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (E : H →L[ℂ] H) (M : ℕ) (h : ∀ g : Fin M → G, stdPoly E (fun i => σ (g i)) = 0)
    (a : Fin M → H →L[ℂ] H)
    (ha : ∀ i, ∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * a i = a i * T) :
    stdPoly E a = 0 := by
  classical
  have step : ∀ j : ℕ, ∀ g : Fin M → G,
      stdPoly E (fun i : Fin M => if (i : ℕ) < j then a i else σ (g i)) = 0 := by
    intro j
    induction j with
    | zero => intro g; simpa using h g
    | succ j ih =>
      intro g
      by_cases hj : j < M
      · let k : Fin M := ⟨j, hj⟩
        let b : Fin M → H →L[ℂ] H := fun i => if (i : ℕ) < j then a i else σ (g i)
        have hb : (fun i : Fin M => if (i : ℕ) < j + 1 then a i else σ (g i)) =
            Function.update b k (a k) := by
          funext i
          by_cases hik : i = k
          · subst hik
            simp [b, k]
          · rw [Function.update_of_ne hik]
            have hne : (i : ℕ) ≠ j := fun e => hik (Fin.ext e)
            by_cases hlt : (i : ℕ) < j
            · have h2 : (i : ℕ) < j + 1 := by omega
              simp [b, hlt, h2]
            · have h2 : ¬ (i : ℕ) < j + 1 := by omega
              simp [b, hlt, h2]
        obtain ⟨A, B, hAB⟩ := CompanionTheory.D.gk.admitted.FinOfPIAux.stdPoly_update E b k
        have hσk : ∀ x : G, stdPoly E (Function.update b k (σ x)) = 0 := by
          intro x
          have hx := ih (Function.update g k x)
          convert hx using 2
          funext i
          by_cases hik : i = k
          · subst hik
            simp [b, k]
          · rw [Function.update_of_ne hik]
            simp [b, Function.update_of_ne hik]
        rw [hb, hAB]
        ext v
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply,
          ContinuousLinearMap.zero_apply]
        refine sum_eq_zero_of_bicomm σ hσ A (fun π => B π v) ?_ (a k) (ha k)
        intro x
        have hv := congrArg (fun S : H →L[ℂ] H => S v) ((hAB (σ x)).symm.trans (hσk x))
        simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply] using hv
      · have hiff : ∀ i : Fin M, ((i : ℕ) < j + 1 ↔ (i : ℕ) < j) := fun i => by
          have := i.isLt
          omega
        simpa [hiff] using ih g
  simpa using step M (fun _ => 1)

theorem stdPoly_bicomm : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (E : H →L[ℂ] H) (m : ℕ), (∀ g : Fin m → G, stdPoly E (fun i => σ (g i)) = 0) →
    ∀ a : Fin m → (H →L[ℂ] H), (∀ i, ∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * a i = a i * T) → stdPoly E a = 0 := by
  intro G H _ _ _ _ σ hσ E m h a ha
  exact standard_polynomial_vanishes_on_bicommutant σ hσ E m h a ha

end GlobalTheory.CompanionTheory.Factor
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StarProjectionCommute
section
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CyclicScalar

theorem inner_map_map {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (g : G) (x y : H) :
    ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ g).toLinearMap (hσ g)).inner_map_map x y

theorem map_inv_map {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (g : G) (x : H) : σ g (σ g⁻¹ x) = x := by
  have h : σ g * σ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact DFunLike.congr_fun h x

theorem orthogonal_stable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (U : Submodule ℂ H)
    (hU : ∀ g, ∀ v ∈ U, σ g v ∈ U) (g : G) (v : H) (hv : v ∈ Uᗮ) : σ g v ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  rw [← map_inv_map σ g u, inner_map_map σ hσ]
  exact hv _ (hU _ _ hu)

theorem starProjection_commute {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection] (hU : ∀ g, ∀ v ∈ U, σ g v ∈ U) (g : G) :
    U.starProjection * σ g = σ g * U.starProjection := by
  ext v
  simp only [ContinuousLinearMap.mul_apply]
  have h1 : U.starProjection v ∈ U := Submodule.starProjection_apply_mem U v
  have h2 : v - U.starProjection v ∈ Uᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have h3 : σ g v = σ g (U.starProjection v) + σ g (v - U.starProjection v) := by
    rw [← map_add (f := _)]; simp
  rw [h3, map_add (f := _), Submodule.starProjection_eq_self_iff.2 (hU g _ h1),
    (Submodule.starProjection_apply_eq_zero_iff U).2 (orthogonal_stable σ hσ U hU g _ h2), add_zero]

theorem exists_isIrredSubrep : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (Q : Submodule ℂ H) (ξ : H), IsClosed (Q : Set H) → ξ ∈ Q → ξ ≠ 0 →
    (∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → ∀ v ∈ Q, T v ∈ Q) →
    (∀ g, ∃ c : ℂ, σ g ξ - c • ξ ∈ Qᗮ) → ∃ W, IsIrredSubrep σ W := by
  intro G H _ _ _ _ σ hσ Q ξ hQ hξQ hξ hcomm hscal
  haveI : CompleteSpace Q := hQ.completeSpace_coe

  let S : Submodule ℂ H := Submodule.span ℂ (Set.range fun g => σ g ξ)
  have hSstable : ∀ g, ∀ v ∈ S, σ g v ∈ S := by
    intro g v hv
    have : S ≤ S.comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      refine Submodule.subset_span ⟨g * h, ?_⟩
      simp [map_mul]
    exact this hv
  have hW : IsSubrep σ S.topologicalClosure := isSubrep_topologicalClosure hSstable
  have horbit : ∀ g, σ g ξ ∈ S.topologicalClosure := fun g =>
    S.le_topologicalClosure (Submodule.subset_span ⟨g, rfl⟩)
  have hξW : ξ ∈ S.topologicalClosure := by simpa using horbit 1

  have hmin : ∀ A : Submodule ℂ H, IsClosed (A : Set H) → (∀ g, σ g ξ ∈ A) → S.topologicalClosure ≤ A := by
    intro A hA h
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) hA
    rintro _ ⟨g, rfl⟩
    exact h g

  have hline : ∀ w ∈ S.topologicalClosure, Q.starProjection w ∈ (ℂ ∙ ξ) := by
    have hclosed : IsClosed (((ℂ ∙ ξ).comap (Q.starProjection : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) :=
      (Submodule.closed_of_finiteDimensional (ℂ ∙ ξ)).preimage Q.starProjection.continuous
    refine fun w hw => hmin _ hclosed (fun g => ?_) hw
    obtain ⟨c, hc⟩ := hscal g
    have e : σ g ξ = c • ξ + (σ g ξ - c • ξ) := by abel
    change Q.starProjection (σ g ξ) ∈ (ℂ ∙ ξ)
    rw [e, map_add (f := _), (Submodule.starProjection_apply_eq_zero_iff Q).2 hc, add_zero, map_smul,
      Submodule.starProjection_eq_self_iff.2 hξQ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self ξ)
  refine ⟨S.topologicalClosure, hW, fun h => hξ (by simpa [h] using hξW), fun U hUW hU => ?_⟩
  haveI : CompleteSpace U := hU.1.completeSpace_coe
  have hPc := starProjection_commute σ hσ U hU.2
  have hPQ : U.starProjection ξ ∈ Q := hcomm _ hPc ξ hξQ
  have hPU : U.starProjection ξ ∈ U := Submodule.starProjection_apply_mem U ξ
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ξ = U.starProjection ξ := by
    have := hline _ (hUW hPU)
    rw [Submodule.starProjection_eq_self_iff.2 hPQ] at this
    exact Submodule.mem_span_singleton.1 this
  have hcc : c * c = c := by
    have h1 : U.starProjection (c • ξ) = c • ξ := by
      rw [hc]; exact Submodule.starProjection_eq_self_iff.2 hPU
    rw [map_smul, ← hc, smul_smul] at h1
    have h2 : (c * c - c) • ξ = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hξ)
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, hcc]; ring
    exact (mul_eq_zero.1 this).imp id sub_eq_zero.1
  rcases hc01 with rfl | rfl
  · left
    have hP0 : U.starProjection ξ = 0 := by rw [← hc, zero_smul]
    have hle : S.topologicalClosure ≤ Uᗮ := by
      refine hmin _ (Submodule.isClosed_orthogonal U) fun g => ?_
      refine (Submodule.starProjection_apply_eq_zero_iff U).1 ?_
      have := DFunLike.congr_fun (hPc g) ξ
      simpa [hP0] using this
    refine (Submodule.eq_bot_iff U).2 fun x hx => ?_
    exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal U x).1 (hle (hUW hx)) x hx)
  · right
    have hξU : ξ ∈ U := by
      rw [one_smul] at hc
      rw [hc]; exact hPU
    exact le_antisymm hUW (hmin _ hU.1 fun g => hU.2 g ξ hξU)

end GlobalTheory.CompanionTheory.CyclicScalar
end

