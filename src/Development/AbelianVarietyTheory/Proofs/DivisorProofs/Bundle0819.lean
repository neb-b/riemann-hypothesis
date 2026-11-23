module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticSubfieldRootDiscriminant
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke Polynomial

namespace GlobalTheory

theorem finrank_eq_two_of_adjoin_sqrt_eq_top (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤) (hsf : Squarefree a) (h1 : a ≠ 1) :
    Module.finrank ℚ K = 2 := by
  have hirr : Irreducible (X ^ 2 - C (a : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (Formalism.HF.P.quad_not_sq_rat a hsf h1)
  have hmon : (X ^ 2 - C (a : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C (a : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have := IntermediateField.adjoin.finrank (K := ℚ) (x := x) (.of_finite ℚ x)
  rw [hmin, natDegree_X_pow_sub_C _, hadj, IntermediateField.finrank_top'] at this
  exact this

theorem adjoin_gen_eq_top_rat {E : Type} [Field E] [NumberField E] (y : E) :
    IntermediateField.adjoin ℚ {IntermediateField.AdjoinSimple.gen ℚ y} = ⊤ := by
  apply IntermediateField.lift_injective
  exact (IntermediateField.lift_adjoin_simple ℚ _ (IntermediateField.AdjoinSimple.gen ℚ y)).trans
    (IntermediateField.lift_top ℚ (IntermediateField.adjoin ℚ {y})).symm

theorem rootDiscr_and_different_quadField :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
      rootDiscr (AdelicDegreeTameRamification.quadField H) = √(H.d : ℝ) ∧
      (differentIdeal ℤ (𝓞 (AdelicDegreeTameRamification.quadField H))).map (algebraMap (𝓞 (AdelicDegreeTameRamification.quadField H)) (𝓞 E)) =
        Ideal.span {H.rt} := by
  intro E _ _ _ H
  have hd16 := H.d_mod
  have hb2 : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  obtain ⟨x, hxdef, hadj⟩ : ∃ x : AdelicDegreeTameRamification.quadField H, (x : E) = (H.rt : E) ∧
      IntermediateField.adjoin ℚ {x} = ⊤ :=
    ⟨IntermediateField.AdjoinSimple.gen ℚ _, rfl, adjoin_gen_eq_top_rat _⟩
  have hx : x ^ 2 = ((-(H.d : ℤ) : ℤ) : AdelicDegreeTameRamification.quadField H) := by
    apply Subtype.ext
    push_cast
    rw [hxdef, hb2]
  have hint : IsIntegral ℤ x := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hx, ← eq_intCast (algebraMap ℤ (AdelicDegreeTameRamification.quadField H))]
    exact isIntegral_algebraMap
  have hsf : Squarefree (-(H.d : ℤ)) := by
    rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.natAbs_natCast]
    exact H.d_prime.squarefree
  obtain ⟨x', hx'⟩ : ∃ x' : 𝓞 (AdelicDegreeTameRamification.quadField H), (x' : AdelicDegreeTameRamification.quadField H) = x := ⟨⟨x, hint⟩, rfl⟩
  have hdiff := Formalism.MainNotions.UnusedSlot33.HK.different_quad (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf
    (by omega) (by omega) x' hx'
  have h2 := finrank_eq_two_of_adjoin_sqrt_eq_top (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf (by omega)
  have hD := Formalism.HF.P.quadDiscr_ne_one (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [rootDiscr_def, h2, hD, Real.sqrt_eq_rpow]
    simp
  · rw [hdiff, Ideal.map_span, Set.image_singleton]
    congr 2
    apply RingOfIntegers.coe_injective
    show ((x' : AdelicDegreeTameRamification.quadField H) : E) = _
    rw [hx', hxdef]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiReflectionPairTruncationMemClosure
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.SUPair
open Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

def wv (x : Fin M → E) : Fin M → E := Matrix.vecMul (fun i => σ (x i)) J

theorem hE_eq (x v : Fin M → E) : hE σ J x v = wv σ J x ⬝ᵥ v := by
  simp only [hE, Formalism.UG.hform, wv, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem qr_eq (x : Fin M → E) (u : E) :
    GlobalTheory.SUAssemble.qr σ J x u = 1 + ((u - 1) / hE σ J x x) • Matrix.vecMulVec x (wv σ J x) := rfl

theorem qr_mulVec (x : Fin M → E) (u : E) (v : Fin M → E) :
    GlobalTheory.SUAssemble.qr σ J x u *ᵥ v = v + ((u - 1) / hE σ J x x * hE σ J x v) • x := by
  rw [qr_eq, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  simp only [hE_eq, op_smul_eq_smul, smul_smul]

theorem hE_sub_left (a b v : Fin M → E) : hE σ J (a - b) v = hE σ J a v - hE σ J b v := by
  simp [hE, Formalism.UG.hform, sub_mul, Finset.sum_sub_distrib]
theorem hE_smul_left (t : E) (a v : Fin M → E) : hE σ J (t • a) v = σ t * hE σ J a v := by
  simp [hE, Formalism.UG.hform, Finset.mul_sum, mul_assoc]
theorem hE_sub_right (a b v : Fin M → E) : hE σ J v (a - b) = hE σ J v a - hE σ J v b := by
  simp [hE, Formalism.UG.hform, mul_sub, Finset.sum_sub_distrib]
theorem hE_smul_right (t : E) (a v : Fin M → E) : hE σ J v (t • a) = t * hE σ J v a := by
  simp [hE, Formalism.UG.hform, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem Q_mul_Q (x : Fin M → E) :
    Matrix.vecMulVec x (wv σ J x) * Matrix.vecMulVec x (wv σ J x) = hE σ J x x • Matrix.vecMulVec x (wv σ J x) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, hE_eq, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => by ring

theorem cT_Q_mul (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E) :
    Formalism.UG.cT (σ : E →+* E) (Matrix.vecMulVec x (wv σ J x)) * J = J * Matrix.vecMulVec x (wv σ J x) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.vecMulVec_apply, wv,
    Matrix.vecMul, dotProduct, map_mul, map_sum, AlgHom.coe_toRingHom, hσ, hJ]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.SUPair

namespace GlobalTheory.SUPair
open Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem hE_self (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E) :
    σ (hE σ J x x) = hE σ J x x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem qr_one (x : Fin M → E) : GlobalTheory.SUAssemble.qr σ J x 1 = 1 := by
  rw [qr_eq, sub_self, zero_div, zero_smul, add_zero]

theorem qr_mul_qr (x : Fin M → E) (hx : hE σ J x x ≠ 0) (a b : E) :
    GlobalTheory.SUAssemble.qr σ J x a * GlobalTheory.SUAssemble.qr σ J x b = GlobalTheory.SUAssemble.qr σ J x (a * b) := by
  rw [qr_eq, qr_eq, qr_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Q_mul_Q, smul_add]
  have : (a * b - 1) / hE σ J x x = (a - 1) / hE σ J x x + (b - 1) / hE σ J x x +
      (a - 1) / hE σ J x x * ((b - 1) / hE σ J x x * hE σ J x x) := by
    field_simp; ring
  rw [this]
  module

theorem cT_qr (x : Fin M → E) (u : E) :
    Formalism.UG.cT (σ : E →+* E) (GlobalTheory.SUAssemble.qr σ J x u) =
      1 + σ ((u - 1) / hE σ J x x) • Formalism.UG.cT (σ : E →+* E) (Matrix.vecMulVec x (wv σ J x)) := by
  rw [qr_eq]
  ext i j
  simp [Formalism.UG.cT, Matrix.one_apply, eq_comm]

theorem qr_unitary (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E)
    (hx : hE σ J x x ≠ 0) (u : E) (hu : u * σ u = 1) :
    Formalism.UG.cT (σ : E →+* E) (GlobalTheory.SUAssemble.qr σ J x u) * J * GlobalTheory.SUAssemble.qr σ J x u = J := by
  rw [cT_qr]
  rw [qr_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, cT_Q_mul σ J hσ hJ, Matrix.mul_assoc, Q_mul_Q, smul_add]
  have hs : σ ((u - 1) / hE σ J x x) = (σ u - 1) / hE σ J x x := by
    rw [map_div₀, map_sub, map_one, hE_self σ J hσ hJ]
  rw [hs]
  have : (u - 1) / hE σ J x x * ((σ u - 1) / hE σ J x x * hE σ J x x) =
      -((σ u - 1) / hE σ J x x) - (u - 1) / hE σ J x x := by
    field_simp; linear_combination hu
  rw [this]
  module

theorem det_qr (x : Fin M → E) (hx : hE σ J x x ≠ 0) (u : E) : (GlobalTheory.SUAssemble.qr σ J x u).det = u := by
  rw [qr_eq, ← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq (ι := Unit),
    Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, ← hE_eq, smul_eq_mul, div_mul_cancel₀ _ hx]
  ring

end GlobalTheory.SUPair

namespace GlobalTheory.SUPair
open Matrix

section Grp
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

def qrU (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E) (hx : hE σ J x x ≠ 0)
    (u : E) (hu : u * σ u = 1) : Formalism.UG.UJ (σ : E →+* E) J :=
  ⟨⟨GlobalTheory.SUAssemble.qr σ J x u, GlobalTheory.SUAssemble.qr σ J x (σ u),
    by rw [qr_mul_qr σ J x hx, hu, qr_one], by rw [qr_mul_qr σ J x hx, mul_comm, hu, qr_one]⟩,
    qr_unitary σ J hσ hJ x hx u hu⟩

end Grp

section Fix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem trunc_fix (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J) (v : Fin M → E)
    (hv : (g.1 : Matrix (Fin M) (Fin M) E) *ᵥ v = v) :
    ((HA.mat (AF F) σ J (GlobalTheory.SUAssemble.trunc σ J η hη g)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *ᵥ
      (fun i => inclR (AF F) (v i)) = fun i => inclR (AF F) (v i) := by
  rw [GlobalTheory.SUAssemble.mv_trunc]
  have h : GlobalTheory.SUAssemble.rmat (F := F) g.1 *ᵥ (fun i => inclR (AF F) (v i)) = fun i => inclR (AF F) (v i) := by
    funext i
    conv_rhs => rw [← hv]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [GlobalTheory.SUAssemble.rmat, Matrix.mulVec, dotProduct, map_sum]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, h, Matrix.one_mulVec, sub_self,
    smul_zero, add_zero]

end Fix

theorem trunc_pair_mem : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (η : AF F) (hη : η * η = η) (x y z : Fin M → E) (u : E), u * σ u = 1 → hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → hE σ J z z ≠ 0 → (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) → (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) → ∃ p : Formalism.UG.UJ (σ : E →+* E) J, (p.1 : Matrix (Fin M) (Fin M) E) = GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J y (σ u) ∧ GlobalTheory.SUAssemble.trunc σ J η hη p ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro H F E _ _ _ _ _ σ hcm M J hJ S₁ S₂ ε hε hne η hη x y z u hu hx hy hz ⟨hz'n, t₁, ht₁⟩ ⟨hy'n, t₂, ht₂⟩
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hJ' : ∀ i j, σ (J j i) = J i j := hJ.1
  have hu' : σ u * σ (σ u) = 1 := by rw [hσ, mul_comm, hu]
  set S := {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} with hS
  have h1 : (1 : HA (AF F) σ J) ∈ closure S := subset_closure ⟨1, (SURat σ J).one_mem, 1,
    (GlobalTheory.SUSuppSub.mem_SUSupp_iff σ J).2 ⟨(SUAdelic σ J).one_mem, by rw [GlobalTheory.SUSuppSub.mv_one, sub_self, smul_zero]⟩,
    by simp⟩
  have hmul : ∀ a ∈ closure S, ∀ b ∈ closure S, a * b ∈ closure S := by
    intro a ha b hb
    have hbi : b⁻¹ ∈ closure S := by
      simpa using GlobalTheory.SUSuppSub.closure_div_mem F E σ hcm M J hJ S₁ S₂ ε hε 1 h1 b hb
    simpa using GlobalTheory.SUSuppSub.closure_div_mem F E σ hcm M J hJ S₁ S₂ ε hε a ha b⁻¹ hbi
  let A := qrU σ J hσ hJ' x hx u hu
  let B := qrU σ J hσ hJ' y hy (σ u) hu'
  let C := qrU σ J hσ hJ' z hz (σ u) hu'
  let D := qrU σ J hσ hJ' z hz u hu
  refine ⟨A * B, rfl, ?_⟩
  have hCD : C * D = 1 := Subtype.ext (Units.ext (by
    show GlobalTheory.SUAssemble.qr σ J z (σ u) * GlobalTheory.SUAssemble.qr σ J z u = 1
    rw [qr_mul_qr σ J z hz, mul_comm, hu, qr_one]))
  have hAB : A * B = (A * C) * (D * B) := by
    rw [mul_assoc, ← mul_assoc C, hCD, one_mul]
  rw [hAB, map_mul]

  have hzv : ∀ v : Fin M → E, hE σ J x v = 0 →
      hE σ J (z - (hE σ J x z / hE σ J x x) • x) v = 0 → hE σ J z v = 0 := by
    intro v h1 h2
    rwa [hE_sub_left, hE_smul_left, h1, mul_zero, sub_zero] at h2
  have hyv : ∀ v : Fin M → E, hE σ J z v = 0 →
      hE σ J (y - (hE σ J z y / hE σ J z z) • z) v = 0 → hE σ J y v = 0 := by
    intro v h1 h2
    rwa [hE_sub_left, hE_smul_left, h1, mul_zero, sub_zero] at h2
  apply hmul
  · refine H F E σ hcm M J hJ S₁ S₂ ε hε hne x (z - (hE σ J x z / hE σ J x x) • x) ?_ hx hz'n ⟨t₁, ht₁⟩ _ ?_ ?_
    · rw [hE_sub_right, hE_smul_right, div_mul_cancel₀ _ hx, sub_self]
    · refine GlobalTheory.SUAssemble.trunc_mem_SUAdelic σ J η hη _ ?_
      show (GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J z (σ u)).det = 1
      rw [Matrix.det_mul, det_qr σ J x hx, det_qr σ J z hz, hu]
    · intro v h1 h2
      refine trunc_fix σ J η hη _ v ?_
      show (GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J z (σ u)) *ᵥ v = v
      rw [← Matrix.mulVec_mulVec, qr_mulVec σ J z, hzv v h1 h2, mul_zero, zero_smul, add_zero, qr_mulVec σ J x, h1, mul_zero,
        zero_smul, add_zero]
  · refine H F E σ hcm M J hJ S₁ S₂ ε hε hne z (y - (hE σ J z y / hE σ J z z) • z) ?_ hz hy'n ⟨t₂, ht₂⟩ _ ?_ ?_
    · rw [hE_sub_right, hE_smul_right, div_mul_cancel₀ _ hz, sub_self]
    · refine GlobalTheory.SUAssemble.trunc_mem_SUAdelic σ J η hη _ ?_
      show (GlobalTheory.SUAssemble.qr σ J z u * GlobalTheory.SUAssemble.qr σ J y (σ u)).det = 1
      rw [Matrix.det_mul, det_qr σ J z hz, det_qr σ J y hy, hu]
    · intro v h1 h2
      refine trunc_fix σ J η hη _ v ?_
      show (GlobalTheory.SUAssemble.qr σ J z u * GlobalTheory.SUAssemble.qr σ J y (σ u)) *ᵥ v = v
      rw [← Matrix.mulVec_mulVec, qr_mulVec σ J y, hyv v h1 h2, mul_zero, zero_smul, add_zero, qr_mulVec σ J z, h1, mul_zero,
        zero_smul, add_zero]

end GlobalTheory.SUPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapOneInjective
section
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open GlobalTheory.PELU
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj imForm imForm_apply herm_add_left herm_add_right
  herm_smul_left herm_smul_right herm_conj riemann_symm eq_zero_of_imForm det_ne_zero_of_pos colMat colMat_apply
  exists_finset_of_mem_nhds)

namespace GlobalTheory.PerCoordU

noncomputable section

variable {g : ℕ}

def Tsp {O : Type} [Ring O] (bar : O → O) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) :
    Submodule ℂ (Matrix (Fin g) (Fin g) ℂ) where
  carrier := {S | Sᵀ = S ∧ ∀ a, S * (ρ (bar a)).map star = (ρ a)ᴴ * S}
  zero_mem' := ⟨by simp, fun a => by simp⟩
  add_mem' := by
    rintro S T ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [transpose_add, h1, h3], fun a => by rw [Matrix.add_mul, Matrix.mul_add, h2, h4]⟩
  smul_mem' := by
    rintro c S ⟨h1, h2⟩
    exact ⟨by rw [transpose_smul, h1], fun a => by rw [Matrix.smul_mul, Matrix.mul_smul, h2]⟩

theorem star_mulVec_map (M : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : star (M *ᵥ z) = M.map star *ᵥ star z := by
  funext i; simp [mulVec, dotProduct]

theorem herm_mulVec_left (M A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M (A *ᵥ z) w = hermForm (Aᵀ * M) z w := by
  unfold hermForm
  rw [← mulVec_mulVec, dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]

theorem herm_mulVec_right (M A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M z (A *ᵥ w) = hermForm (M * A.map star) z w := by
  unfold hermForm
  rw [star_mulVec_map, mulVec_mulVec]

theorem herm_single (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (i j : Fin g) :
    hermForm M (Pi.single i c) (Pi.single j 1) = c * M i j := by
  simp [hermForm, ← Pi.single_star, mulVec_single]

theorem sesq_ext {N N' : Matrix (Fin g) (Fin g) ℂ} (h : ∀ z w, (hermForm N z w).im = (hermForm N' z w).im) : N = N' := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have h2 := h (Pi.single i Complex.I) (Pi.single j 1)
  simp only [herm_single] at h1 h2
  simp at h1 h2
  apply Complex.ext <;> linarith

variable {O : Type} [Ring O] {bar : O → O} {D : PLat O bar} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}

theorem ext_per {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ρ P) {W : Type} [AddCommGroup W] [Module ℝ W]
    {f f' : (Fin g → ℂ) →ₗ[ℝ] W} (h : ∀ x, f (P x) = f' (P x)) : f = f' :=
  LinearMap.ext_on_range hP.2.2.2.1 h

theorem relation_per {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P) (c : D.La →₀ ℝ)
    (hc : Finsupp.linearCombination ℝ P₀ c = 0) : Finsupp.linearCombination ℝ P c = 0 := by
  obtain ⟨M₀, -, -, h₀⟩ := hP₀.2.2.2.2
  obtain ⟨M, -, hpos, h⟩ := hP.2.2.2.2
  refine eq_zero_of_imForm hpos (ext_per hP fun y => ?_)
  have := congrArg (fun u => imForm M₀ u (P₀ y)) hc
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, imForm_apply, h, h₀, map_zero, LinearMap.zero_apply] at this ⊢
  exact this

theorem exists_colMat_per {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) :
    ∃ α β : Fin g → (D.La →₀ ℂ), ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D ρ P →
      ∀ x, P x = realMap (colMat α P) (colMat β P) (P₀ x) := by
  have hs : ∀ z : Fin g → ℂ, ∃ c : D.La →₀ ℝ, Finsupp.linearCombination ℝ P₀ c = z := fun z => by
    have : z ∈ Submodule.span ℝ (Set.range P₀) := by rw [hP₀.2.2.2.1]; trivial
    rwa [← Finsupp.range_linearCombination] at this
  choose r hr using fun j => hs (Pi.single j 1)
  choose r' hr' using fun j => hs (Pi.single j Complex.I)
  let k : (D.La →₀ ℝ) → (D.La →₀ ℂ) := Finsupp.mapRange (fun t => (t : ℂ)) (by simp)
  have hk : ∀ (f : D.La → Fin g → ℂ) c, Finsupp.linearCombination ℂ f (k c) = Finsupp.linearCombination ℝ f c :=
    fun f c => by
      simp only [Finsupp.linearCombination_apply, k]
      rw [Finsupp.sum_mapRange_index (by simp)]
      rfl
  refine ⟨fun j => (1 / 2 : ℂ) • k (r j) - (Complex.I / 2) • k (r' j),
    fun j => (1 / 2 : ℂ) • k (r j) + (Complex.I / 2) • k (r' j), fun P hP x => ?_⟩
  have := relation_per hP₀ hP (Finsupp.single x 1 - ∑ j, ((P₀ x j).re • r j + (P₀ x j).im • r' j)) (by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_add (f := _), map_smul, hr, hr', Finsupp.linearCombination_single, one_smul]
    funext i
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_add (f := _), map_smul, Finsupp.linearCombination_single, one_smul, sub_eq_zero] at this
  rw [this]
  funext i
  simp only [realMap_apply, Pi.add_apply, mulVec, dotProduct, colMat_apply, map_sub, map_add (f := _), map_smul, hk,
    Finset.sum_apply, ← Finset.sum_add_distrib, Pi.smul_apply, Pi.sub_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  apply Complex.ext <;> simp <;> ring

theorem comm_realMap_per {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (a : O) :
    ρ a * A = A * ρ a ∧ ρ a * B = B * (ρ a).map star := by
  refine realMap_inj (ext_per hP₀ fun x => ?_)
  have := h (a • x)
  rw [hP.1, hP₀.1, h] at this
  simp only [realMap_apply, mulVec_add, mulVec_mulVec, star_mulVec_map] at this ⊢
  exact this

theorem comm_herm_per {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) {M : Matrix (Fin g) (Fin g) ℂ}
    (hM : ∀ x y, (hermForm M (P₀ x) (P₀ y)).im = D.EF x y) (a : O) :
    (ρ a)ᵀ * M = M * (ρ (bar a)).map star := by
  have key : (imForm M).compl₁₂ (realMap (ρ a) 0) LinearMap.id =
      (imForm M).compl₁₂ LinearMap.id (realMap (ρ (bar a)) 0) := by
    refine ext_per hP₀ fun x => ext_per hP₀ fun y => ?_
    simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
      ← hP₀.1, imForm_apply, hM, D.adj]
  refine sesq_ext fun z w => ?_
  have := LinearMap.congr_fun₂ key z w
  simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
    imForm_apply] at this
  rw [← herm_mulVec_left, ← herm_mulVec_right]
  exact this

theorem map_star_transpose (M : Matrix (Fin g) (Fin g) ℂ) : (M.map star)ᵀ = Mᴴ := rfl

theorem mem_Tsp_of_period {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P)
    {M₀ : Matrix (Fin g) (Fin g) ℂ} (hM₀ : ∀ x y, (hermForm M₀ (P₀ x) (P₀ y)).im = D.EF x y)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (hA : A.det ≠ 0) :
    (A⁻¹ * B)ᵀ * M₀ ∈ Tsp bar ρ := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨M, hM, -, hE⟩ := hP.2.2.2.2
    have key : (imForm M).compl₁₂ (realMap A B) (realMap A B) = imForm M₀ := by
      refine ext_per hP₀ fun x => ext_per hP₀ fun y => ?_
      simp only [LinearMap.compl₁₂_apply, ← h, imForm_apply, hE, hM₀]
    ext i j
    rw [transpose_apply]
    refine riemann_symm (M := Aᵀ * M * A.map star) ?_ (fun z w => ?_) j i
    · have := isHermitian_conjTranspose_mul_mul (A.map star) hM
      convert this using 3
      ext i j; simp
    · rw [GlobalTheory.PeriodConn.hermForm_conj_mul]
      simp only [mulVec_add, mulVec_mulVec, mul_nonsing_inv_cancel_left _ _ hu]
      exact LinearMap.congr_fun₂ key z w
  · obtain ⟨h1, h2⟩ := comm_realMap_per hP₀ hP h a
    have h3 : ρ a * (A⁻¹ * B) = A⁻¹ * B * (ρ a).map star := by
      rw [Matrix.mul_assoc, ← h2]
      have : A⁻¹ * (ρ a * A) * A⁻¹ = A⁻¹ * (A * ρ a) * A⁻¹ := by rw [h1]
      rw [nonsing_inv_mul_cancel_left _ _ hu, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hu] at this
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, this]
    rw [Matrix.mul_assoc, ← comm_herm_per hP₀ hM₀ a, ← Matrix.mul_assoc, ← transpose_mul, h3, transpose_mul,
      map_star_transpose, Matrix.mul_assoc]

theorem comm_of_mem_Tsp {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) {M₀ : Matrix (Fin g) (Fin g) ℂ}
    (hM₀ : ∀ x y, (hermForm M₀ (P₀ x) (P₀ y)).im = D.EF x y) (hdet : M₀.det ≠ 0) {C : Matrix (Fin g) (Fin g) ℂ}
    (hC : Cᵀ * M₀ ∈ Tsp bar ρ) (a : O) : ρ a * C = C * (ρ a).map star := by
  have hu : IsUnit M₀.det := isUnit_iff_ne_zero.mpr hdet
  have h := hC.2 a
  rw [Matrix.mul_assoc, ← comm_herm_per hP₀ hM₀ a, ← Matrix.mul_assoc, ← transpose_mul, ← map_star_transpose,
    ← Matrix.mul_assoc, ← transpose_mul] at h
  have := congrArg (· * M₀⁻¹) h
  simp only [mul_nonsing_inv_cancel_right _ _ hu] at this
  exact transpose_injective this

theorem realMap_one_injective {C : Matrix (Fin g) (Fin g) ℂ} (h : (1 - C * C.map star).det ≠ 0) :
    Function.Injective (realMap 1 C) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  rw [realMap_apply, one_mulVec] at hz
  have h1 : z = -(C *ᵥ star z) := eq_neg_of_add_eq_zero_left hz
  have h2 : star z = -(C.map star *ᵥ z) := by
    have := congrArg star hz
    rw [star_add, star_mulVec_map, star_star, star_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  refine eq_zero_of_mulVec_eq_zero h ?_
  rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, ← neg_neg (C.map star *ᵥ z), ← h2, mulVec_neg, ← h1, sub_self]

end

end GlobalTheory.PerCoordU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivOfIsLBSplitTorus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TorusPic

theorem triv_of_isLB_splitTorus : ∀ (A : Type) [CommRing A], IsField A → ∀ (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : LB (splitTorus (Sp A) X).left), N.IsLB → Triv N := by
  intro A _ hA X _ _ _ N hN
  letI := hA.toField
  have : IsAffine (splitTorus (Sp A) X).left := by
    have := Diag.isAffineHom_hom (Sp A) X
    exact isAffine_of_isAffineHom (splitTorus (Sp A) X).hom
  have := GlobalTheory.SS.LiftTorus.subsingleton_pic_torus A X
  exact GlobalTheory.LB.exists_isGen_of_subsingleton_pic_top hN

end GlobalTheory.TorusPic
end
end

