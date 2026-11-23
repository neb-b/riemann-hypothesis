module

public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLx
public import Mathlib
public import Formalism.FormalDegreeBessel.FinalDS
public import Formalism.SharpRestriction.CuspSpanNormBounds.KTwoMinorIntegrality
public import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedLatticeSum

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
section
open MeasureTheory Finset
open scoped Matrix

noncomputable section

namespace Formalism.MainNotions.DiscreteSeriesWeylDimension

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def HasTypeU (k : ℕ) (u : Fin k → ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π

def HighestWeightExists : Prop := ∀ (k : ℕ) (u : Fin k → ℝ), Formalism.QuantumDeterminants.IsHCParam u → HasTypeU k u

section Family

variable {eps : ℝ} (Fm : FamP eps)

end Family

section SmallRank

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end SmallRank

section FamilyDS

variable {eps : ℝ} (Fm : FamP eps)

end FamilyDS

def WeylForK : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Formalism.REAL.Kset ε) σ → IsKTypeOf ε σ Λ S →
    (Module.finrank ℂ S : ℝ) =
      (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
        ((Λ + Formalism.REAL.rhoC ε) a - (Λ + Formalism.REAL.rhoC ε) b)) /
      ((∏ i ∈ Finset.range (LocalBesselAndTopKernel.nPl ε), (i.factorial : ℝ)) * ∏ i ∈ Finset.range (LocalBesselAndTopKernel.nMi ε), (i.factorial : ℝ))

def LowKMultOne : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    ∀ S S' : Submodule ℂ H, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S → IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S'

section FamilyRk

variable {eps : ℝ} (Fm : FamP eps)

end FamilyRk

section FamilyExp

variable {eps : ℝ} (Fm : FamP eps)

end FamilyExp

section FamilyExp2

variable {eps : ℝ} (Fm : FamP eps)

end FamilyExp2

section FamilyRigid

variable {eps : ℝ} (Fm : FamP eps)

end FamilyRigid

section FiniteOrder

open Polynomial

end FiniteOrder

section FiniteOrderMat

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] {N : Type*} [Fintype N] [DecidableEq N]

end FiniteOrderMat

end Formalism.MainNotions.DiscreteSeriesWeylDimension

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.KTwoCosetCount
section
noncomputable section

namespace Formalism.MainNotions.KTwoCosetCount

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section A

variable {D : D7}

theorem card_ends_le (j : ℕ) (δ : ℕ → D.host.E) : (KappaEndpoints.k2ends D j δ).card ≤ j := by
  classical
  unfold KappaEndpoints.k2ends
  calc _ ≤ (Finset.Icc 1 j).card := Finset.card_filter_le _ _
    _ = j := by simp

theorem sg_rpow_le (H1 : ℝ) {j : ℕ} (hj : j ≤ D.R.rS) (δ : ℕ → D.host.E) (τ : D.what₂.Tau) :
    KappaEndpoints.k2sg D H1 j δ τ ^ (-(3 * (D.R.rS : ℝ))) ≤
      ∏ l ∈ KappaEndpoints.k2ends D j δ,
        (max 1 (absReal D.host.rdE (embS D τ) D.R.rS l (δ l) / (2 * H1) ^ (2 * D.R.rS))) ^ (-(3 : ℝ)) := by
  set σ := KappaEndpoints.k2sg D H1 j δ τ with hσ
  have h1 : 1 ≤ σ := KappaEndpoints.one_le_minor_sigma H1 j δ τ
  have hle : ∀ l ∈ KappaEndpoints.k2ends D j δ,
      max 1 (absReal D.host.rdE (embS D τ) D.R.rS l (δ l) / (2 * H1) ^ (2 * D.R.rS)) ≤ σ := by
    intro l hl
    refine max_le h1 ?_
    rw [hσ]
    unfold KappaEndpoints.k2sg
    exact (Finset.le_fold_max _).2 (Or.inr ⟨l, hl, le_rfl⟩)
  have step1 : ∏ l ∈ KappaEndpoints.k2ends D j δ, σ ^ (-(3 : ℝ)) ≤
      ∏ l ∈ KappaEndpoints.k2ends D j δ,
        (max 1 (absReal D.host.rdE (embS D τ) D.R.rS l (δ l) / (2 * H1) ^ (2 * D.R.rS))) ^ (-(3 : ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro l _; exact Real.rpow_nonneg (by linarith) _
    · intro l hl
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) (hle l hl) (by norm_num)
  have hc := card_ends_le (D := D) j δ
  have step0 : σ ^ (-(3 * (D.R.rS : ℝ))) ≤ ∏ l ∈ KappaEndpoints.k2ends D j δ, σ ^ (-(3 : ℝ)) := by
    rw [Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    apply Real.rpow_le_rpow_of_exponent_le h1
    have : ((KappaEndpoints.k2ends D j δ).card : ℝ) ≤ D.R.rS := by exact_mod_cast hc.trans hj
    nlinarith
  exact step0.trans step1

end A

section B

variable {D : D7}

def wl (H1 : ℝ) (l : ℕ) (x : D.host.E) : ℝ :=
  ∏ τ : D.what₂.Tau, (max 1 (absReal D.host.rdE (embS D τ) D.R.rS l x / (2 * H1) ^ (2 * D.R.rS))) ^ (-(3 : ℝ))

theorem wl_nonneg (H1 : ℝ) (l : ℕ) (x : D.host.E) : 0 ≤ wl (D := D) H1 l x := Finset.prod_nonneg (fun τ _ => Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)

theorem S_rpow_le (H1 : ℝ) {j : ℕ} (hj : j ≤ D.R.rS) (δ : ℕ → D.host.E) :
    KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ ∏ l ∈ KappaEndpoints.k2ends D j δ, wl (D := D) H1 l (δ l) := by
  unfold KappaEndpoints.k2S wl
  rw [← Real.finsetProd_rpow _ _ (fun τ _ => le_trans zero_le_one (KappaEndpoints.one_le_minor_sigma H1 j δ τ)), Finset.prod_comm]
  exact Finset.prod_le_prod₀ (fun τ _ => Real.rpow_nonneg (le_trans zero_le_one (KappaEndpoints.one_le_minor_sigma H1 j δ τ)) _)
    (fun τ _ => sg_rpow_le H1 hj δ τ)

def Rl (H1 : ℝ) (l : ℕ) : ℝ := max 1 (D.host.rdE ^ ((2 * frameExp D.R.rS l : ℕ) : ℝ) * (2 * H1) ^ (2 * D.R.rS))

theorem one_le_Rl (H1 : ℝ) (l : ℕ) : 1 ≤ Rl (D := D) H1 l := le_max_left _ _

theorem wl_le (hrd : 0 < D.host.rdE) {H1 : ℝ} (hH : 0 < H1) (l : ℕ) (x : D.host.E) :
    wl (D := D) H1 l x ≤ ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / Rl (D := D) H1 l)) ^ (-(3 : ℝ)) := by
  unfold wl
  refine Finset.prod_le_prod₀ (fun τ _ => Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (fun τ _ => ?_)
  apply Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) _ (by norm_num)
  apply max_le_max le_rfl
  have hP : 0 < D.host.rdE ^ ((2 * frameExp D.R.rS l : ℕ) : ℝ) * (2 * H1) ^ (2 * D.R.rS) :=
    mul_pos (Real.rpow_pos_of_pos hrd _) (pow_pos (by linarith) _)
  have e : absReal D.host.rdE (embS D τ) D.R.rS l x / (2 * H1) ^ (2 * D.R.rS) =
      ‖embS D τ x‖ / (D.host.rdE ^ ((2 * frameExp D.R.rS l : ℕ) : ℝ) * (2 * H1) ^ (2 * D.R.rS)) := by
    unfold absReal
    rw [Real.rpow_neg hrd.le]
    push_cast
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hP (le_max_right _ _)

theorem sum_one_coord (hNT : KTwoMinorIntegrality.NormLB) (hLS : KTwoMinorIntegrality.LatSum) [Nonempty D.what₂.Tau] (A : Finset D.host.E)
    (hA : ∀ x ∈ A, IsIntegral ℤ x) {R : ℝ} (hR : 1 ≤ R) :
    ∑ x ∈ A, ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / R)) ^ (-(3 : ℝ)) ≤ (64 * R) ^ (2 * Fintype.card D.what₂.Tau) := by
  classical
  set vec : D.host.E → D.what₂.Tau → ℂ := fun x τ => embS D τ x with hvec
  have hinj : Set.InjOn vec A := by
    intro x _ y _ hxy
    obtain ⟨τ⟩ := (inferInstance : Nonempty D.what₂.Tau)
    exact (embS D τ).injective (congrFun hxy τ)
  have hsum : ∑ x ∈ A, ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / R)) ^ (-(3 : ℝ)) =
      ∑ p ∈ A.image vec, ∏ τ : D.what₂.Tau, (max 1 (‖p τ‖ / R)) ^ (-(3 : ℝ)) := by
    rw [Finset.sum_image hinj]
  rw [hsum]
  apply hLS D.what₂.Tau (A.image vec) R hR
  intro p hp q hq hpq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hq
  have hxy : x - y ≠ 0 := sub_ne_zero.2 (fun h => hpq (by rw [h]))
  have h := hNT D (x - y) ((hA x hx).sub (hA y hy)) hxy
  have e : ∏ τ : D.what₂.Tau, ‖embS D τ (x - y)‖ ^ 2 = (∏ τ : D.what₂.Tau, ‖vec x τ - vec y τ‖) ^ 2 := by
    rw [← Finset.prod_pow]
    simp [hvec, map_sub]
  rw [e] at h
  have h0 : 0 ≤ ∏ τ : D.what₂.Tau, ‖vec x τ - vec y τ‖ := Finset.prod_nonneg fun τ _ => norm_nonneg _
  nlinarith

end B

section C

theorem sum_prod_le {ι α : Type*} [DecidableEq ι] [DecidableEq α] (S : Finset ι) (T : Finset (ι → α)) (g : ι → α → ℝ)
    (hg : ∀ i a, 0 ≤ g i a) (hinj : ∀ δ ∈ T, ∀ δ' ∈ T, (∀ i ∈ S, δ i = δ' i) → δ = δ') :
    ∑ δ ∈ T, ∏ i ∈ S, g i (δ i) ≤ ∏ i ∈ S, ∑ a ∈ T.image (fun δ => δ i), g i a := by
  classical
  rw [Finset.prod_sum]
  let φ : (ι → α) → (∀ i ∈ S, α) := fun δ i _ => δ i
  have hφinj : ∀ δ ∈ T, ∀ δ' ∈ T, φ δ = φ δ' → δ = δ' := fun δ hδ δ' hδ' h =>
    hinj δ hδ δ' hδ' (fun i hi => congrFun (congrFun h i) hi)
  have hsub : T.image φ ⊆ S.pi (fun i => T.image (fun δ => δ i)) := by
    intro x hx
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_pi.mpr (fun i _ => Finset.mem_image_of_mem _ hδ)
  calc ∑ δ ∈ T, ∏ i ∈ S, g i (δ i)
      = ∑ x ∈ T.image φ, ∏ i ∈ S.attach, g i (x i i.2) := by
        rw [Finset.sum_image hφinj]
        refine Finset.sum_congr rfl (fun δ _ => ?_)
        exact (Finset.prod_attach S (fun i => g i (δ i))).symm
    _ ≤ ∑ x ∈ S.pi (fun i => T.image (fun δ => δ i)), ∏ i ∈ S.attach, g i (x i i.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun x _ _ => Finset.prod_nonneg (fun i _ => hg _ _))

end C

section Dsum

variable {D : D7}

end Dsum

end Formalism.MainNotions.KTwoCosetCount

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.LatticeSumBound
section
noncomputable section

namespace Formalism.MainNotions.LatticeSumConvergence

theorem LatSum_holds : Formalism.MainNotions.KTwoMinorIntegrality.LatSum :=
  fun ι _ P R hR hsep => Formalism.MainNotions.WeightedLatticeSum.latSum ι P R hR hsep

end Formalism.MainNotions.LatticeSumConvergence

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.MinorIntegralityTorus
section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.MinorIntegralityTorus

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

theorem prod_norm_emb_eq_abs_norm {K : Type*} [Field K] [NumberField K] (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have h2 : ∏ σ : K →+* ℂ, σ x = ∏ σ : K →ₐ[ℚ] ℂ, σ x :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)
  calc ∏ σ : K →+* ℂ, ‖σ x‖ = ‖∏ σ : K →+* ℂ, σ x‖ := (norm_prod _ _).symm
    _ = ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ := by rw [h2, h]
    _ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by simp

theorem one_le_abs_norm {K : Type*} [Field K] [NumberField K] (x : K) (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    1 ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  set y : 𝓞 K := ⟨x, hx⟩ with hy_def
  have hy : y ≠ 0 := by
    intro h
    apply h0
    first
    | exact congrArg Subtype.val h
    | simpa [y] using congrArg (algebraMap (𝓞 K) K) h
  have hN : Algebra.norm ℤ y ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
  have hc : ((Algebra.norm ℤ y : ℤ) : ℚ) = Algebra.norm ℚ x := Algebra.coe_norm_int y
  rw [← hc]
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ y| := Int.one_le_abs hN
  exact_mod_cast h1

theorem prod_cm {K : Type*} [Field K] [NumberField K] (Φ : Set (K →+* ℂ))
    (hΦ : ∀ φ : K →+* ℂ, φ ∈ Φ ↔ (starRingEnd ℂ).comp φ ∉ Φ) (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = ∏ σ ∈ Finset.univ.filter (· ∈ Φ), ‖σ x‖ ^ 2 := by
  have cc : ∀ σ : K →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := by
    intro σ
    ext z
    simp
  have hinj : Set.InjOn (fun φ : K →+* ℂ => (starRingEnd ℂ).comp φ)
      ↑(Finset.univ.filter (· ∈ Φ)) := by
    intro a _ c _ hab
    ext z
    have h1 := congrArg (fun ψ : K →+* ℂ => ψ z) hab
    simp only [RingHom.comp_apply] at h1
    exact (starRingEnd ℂ).injective h1
  have hc : (Finset.univ.filter (· ∈ Φ))ᶜ =
      (Finset.univ.filter (· ∈ Φ)).image (fun φ : K →+* ℂ => (starRingEnd ℂ).comp φ) := by
    ext σ
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hσ
      refine ⟨(starRingEnd ℂ).comp σ, ?_, cc σ⟩
      rw [hΦ, cc]
      exact hσ
    · rintro ⟨τ, hτ, rfl⟩
      exact (hΦ τ).1 hτ
  rw [← Finset.prod_mul_prod_compl (Finset.univ.filter (· ∈ Φ)), hc, Finset.prod_image hinj,
    Finset.prod_pow, sq]
  congr 1
  apply Finset.prod_congr rfl
  intro σ _
  simp

theorem NormLB_holds : Formalism.MainNotions.KTwoMinorIntegrality.NormLB := by
  intro D x hx h0
  have hcm := D.host.der.cmType
  have hemb := Formalism.BasicNotions.factEmb D.R D.host
  have hre : ∏ τ : D.what₂.Tau, ‖embS D τ x‖ ^ 2 =
      ∏ σ ∈ Finset.univ.filter (· ∈ D.host.cmType), ‖σ x‖ ^ 2 := by
    refine Finset.prod_bij (fun τ _ => embS D τ) ?_ ?_ ?_ ?_
    · intro τ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hemb.2 _).2 (D.eTau τ).2
    · intro τ₁ _ τ₂ _ h
      have h' := hemb.1.1 h
      exact D.eTau.injective (Subtype.ext h')
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      obtain ⟨g, rfl⟩ := hemb.1.2 σ
      have hg : g ∈ D.R.Psi := (hemb.2 g).1 hσ
      exact ⟨D.eTau.symm ⟨g, hg⟩, Finset.mem_univ _, by simp [embS]⟩
    · intro τ _
      rfl
  rw [hre, ← prod_cm _ hcm.1 x, prod_norm_emb_eq_abs_norm]
  exact one_le_abs_norm x hx h0

theorem one_mem_zpow {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) (hI : I ≠ ⊥) (n : ℕ) :
    (1 : K) ∈ ((I : FractionalIdeal (nonZeroDivisors R) K) ^ (-(n : ℤ))) := by
  rw [zpow_neg, zpow_natCast]
  have hne : ((I : FractionalIdeal (nonZeroDivisors R) K) ^ n) ≠ 0 :=
    pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr hI)
  rw [FractionalIdeal.mem_inv_iff hne]
  intro y hy
  rw [one_mul]
  have hle : ((I : FractionalIdeal (nonZeroDivisors R) K) ^ n) ≤ 1 := by
    rw [← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one
  exact hle hy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fr

variable (D : D7)

theorem ddS_ideal_ne : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :
    Ideal (𝓞 D.host.E)) ≠ ⊥ := by
  exact Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

theorem e_mem_XS {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) : F0.e a ∈ XS D F0 := by
  unfold XS ddS
  apply Submodule.subset_span
  refine ⟨a, 1, ?_, (one_smul _ _).symm⟩
  convert one_mem_zpow _ (ddS_ideal_ne D) (D.R.rS - (a : ℕ))
  have := a.isLt
  omega

theorem e_mem_lam {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (hS D).V) (F : LFlag (D.sp.Y 0) D.R.rS T)
    (hX : XLam Λ F = XS D F.fl) (a : Fin D.R.rS) : F.fl.e a ∈ Λ := by
  unfold XLam at hX
  have h := e_mem_XS D F.fl a
  rw [← hX] at h
  exact (Submodule.mem_inf.mp h).1

theorem pair_int {Λ : Submodule (𝓞 D.host.E) (hS D).V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ)
    {x y : (hS D).V} (hx : x ∈ Λ) (hy : y ∈ Λ) : IsIntegral ℤ ((hS D).hT y x) := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular at hU
  rw [← hU] at hx
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at hx
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hx
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hx y hy)
  have hr' : ((hS D).hT y) x = algebraMap (𝓞 D.host.E) D.host.E r := hr.symm
  rw [hr']
  first
  | exact r.2
  | exact RingOfIntegers.isIntegral_coe r
  | exact RingOfIntegers.isIntegral r

end Fr

theorem det_isIntegral {E : Type*} [Field E] {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n E)
    (h : ∀ i j, IsIntegral ℤ (M i j)) : IsIntegral ℤ M.det := by
  let M' : Matrix n n (integralClosure ℤ E) := fun i j => ⟨M i j, h i j⟩
  have hM : (integralClosure ℤ E).val.toRingHom.mapMatrix M' = M := by
    ext i j
    rfl
  rw [← hM, ← RingHom.map_det]
  exact (M'.det).2

end Formalism.MainNotions.MinorIntegralityTorus

end
end

