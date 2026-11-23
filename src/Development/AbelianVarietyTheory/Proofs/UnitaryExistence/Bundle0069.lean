module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndSign
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

theorem level_good_and_sign : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ p : ℕ, p.Prime → Q.l.GoodAt p) ∧ Q.l.A = 1 ∧ ∀ τ : D.host.E →+* ℂ, τ (Q.H.rt : D.host.E) = Q.H.rt0 → (τ (-D.host.xi0)).im < 0 := by
  rintro D Q ⟨⟨-, hrt, hrt0, -⟩, ⟨hM, hA⟩, -, -⟩
  refine ⟨fun p hp => ?_, hA, fun τ hτ => ?_⟩
  · have hodd := Q.l.odd
    rw [hM] at hodd
    have h3 : ∀ a : ℕ, a.Prime → Odd a → 3 ≤ a := fun a ha ho => by
      have h2 := ha.two_le
      obtain ⟨k, hk⟩ := ho
      omega
    have ha := h3 _ (D.host.g_prime 0) (Nat.Odd.of_mul_left hodd)
    have hb := h3 _ (D.host.g_prime 1) (Nat.Odd.of_mul_right hodd)
    have hab : (D.host.g 0).Coprime (D.host.g 1) :=
      (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt
    have hM0 : Q.l.M ≠ 0 := by have := Q.l.three_le; omega
    have key : ∀ c, 3 ≤ c → c ∣ Q.l.M → ¬ p ∣ c → 3 ≤ Q.l.M / p ^ Q.l.M.factorization p :=
      fun c hc hd hn => hc.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd hn))
    by_cases h : p ∣ D.host.g 0
    · refine key _ hb (hM ▸ dvd_mul_left _ _) fun h' => hp.one_lt.ne' ?_
      exact Nat.eq_one_of_dvd_coprimes hab h h'
    · exact key _ ha (hM ▸ dvd_mul_right _ _) h
  · rw [hrt, hrt0] at hτ
    have h1 := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
    have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
      rw [hφ]
      have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
      simpa using hd
    rw [if_pos hpos, Int.cast_one, _root_.one_mul] at h1
    rw [map_neg, Complex.neg_im]
    linarith

end GlobalTheory.RecDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReindexUnitary
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.MarkUnit

theorem infMat_unitary {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) (θ : Ainf F ⊗[F] E →+* ℂ) (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (h : HA (AF F) σ J) :
    ((Formalism.MainNotions.StandardLattice.infMat σ J θ h).map (starRingEnd ℂ)).transpose * J.map τ * Formalism.MainNotions.StandardLattice.infMat σ J θ h =
      J.map τ := by
  let φ : AF F ⊗[F] E →+* ℂ :=
    θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have hφ : ∀ (a : AF F) (x : E), φ (a ⊗ₜ x) =
      GlobalTheory.InfAdeleCM.ext (τ.comp (algebraMap F E)) (fstA F a) * τ x := fun a x =>
    GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2 (fstA F a) x
  have h1 : ∀ z, φ (sigR (AF F) σ z) = starRingEnd ℂ (φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have : sigR (AF F) σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl
      rw [this, hφ, hφ, map_mul, GlobalTheory.InfAdeleCM.conj_ext, hτ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h2 : ∀ x, φ (inclR (AF F) x) = τ x := by
    intro x
    have : inclR (F := F) (AF F) x = (1 : AF F) ⊗ₜ x := rfl
    rw [this, hφ, map_one, map_one, one_mul]
  have hu : Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J h).1 * JR (AF F) J * (HA.mat (AF F) σ J h).1 =
      JR (AF F) J := (show HR (AF F) σ J from h).2
  have hm : Formalism.MainNotions.StandardLattice.infMat σ J θ h = (HA.mat (AF F) σ J h).1.map φ := rfl
  have hJ : (JR (AF F) J).map φ = J.map τ := by
    ext a b
    exact h2 _
  have hc : (Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J h).1).map φ =
      (((HA.mat (AF F) σ J h).1.map φ).map (starRingEnd ℂ)).transpose := by
    ext a b
    exact h1 _
  have := congrArg (fun m => Matrix.map m φ) hu
  simp only [Matrix.map_mul] at this
  rw [hJ, hc] at this
  rw [hm]
  exact this


end GlobalTheory.MarkUnit
end

