module

public import Mathlib
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
public import GroundTheory.GlobalFields.ClassFieldConsequences.RayClass
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup

@[expose] public section

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped RestrictedProduct

namespace GroundTheory.Automorphic

noncomputable section

namespace AdelicGLn

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

def detClassSubgroup (U : Subgroup (FiniteAdelicGL K n)) :
    Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔
    U.map (Matrix.GeneralLinearGroup.det : FiniteAdelicGL K n →* (FiniteAdeleRing (𝓞 K) K)ˣ)

variable {K n}

theorem det_diagonalGL {R : Type*} [CommRing R] (d : Fin n → Rˣ) :
    Matrix.GeneralLinearGroup.det (diagonalGL d) = ∏ k, d k := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagonalGL, det_diagonal, Units.coe_prod]

theorem det_diagonalGL_mulSingle {R : Type*} [CommRing R] (hn : 0 < n) (a : Rˣ) :
    Matrix.GeneralLinearGroup.det (diagonalGL (Pi.mulSingle (⟨0, hn⟩ : Fin n) a)) = a := by
  rw [det_diagonalGL, Finset.prod_pi_mulSingle', if_pos (Finset.mem_univ _)]

theorem exists_eq_finiteDiagonal_mul_mul (hn : 0 < n) {U : Subgroup (FiniteAdelicGL K n)}
    (hU : IsOpen (U : Set (FiniteAdelicGL K n))) {g g' : FiniteAdelicGL K n}
    (h : (Matrix.GeneralLinearGroup.det g)⁻¹ * Matrix.GeneralLinearGroup.det g' ∈
      detClassSubgroup K n U) :
    ∃ γ : GL (Fin n) K, ∃ u ∈ U, g' = finiteDiagonal K n γ * g * u := by
  obtain ⟨_, ⟨κ, rfl⟩, _, ⟨u₀, hu₀, rfl⟩, hκ⟩ := Subgroup.mem_sup.1 h
  set δ : GL (Fin n) K := diagonalGL (Pi.mulSingle (⟨0, hn⟩ : Fin n) κ)
  set g₁ : FiniteAdelicGL K n := finiteDiagonal K n δ * g * u₀
  have hg₁ : Matrix.GeneralLinearGroup.det g₁ = Matrix.GeneralLinearGroup.det g' := by
    simp only [g₁, map_mul, det_finiteDiagonal, δ, det_diagonalGL_mulSingle hn]
    rw [mul_comm _ (Matrix.GeneralLinearGroup.det g), mul_assoc, hκ, mul_inv_cancel_left]
  set x : FiniteAdelicGL K n := g' * g₁⁻¹
  have hx : Matrix.GeneralLinearGroup.det x = 1 := by
    rw [map_mul, map_inv, ← hg₁, mul_inv_cancel]
  have hcont : Continuous fun h : FiniteAdelicGL K n => g₁⁻¹ * h⁻¹ * x * g₁ :=
    ((continuous_const.mul continuous_inv).mul continuous_const).mul continuous_const
  have hx1 : g₁⁻¹ * x⁻¹ * x * g₁ = 1 := by group
  have hO : (fun h : FiniteAdelicGL K n => g₁⁻¹ * h⁻¹ * x * g₁) ⁻¹' (U : Set (FiniteAdelicGL K n)) ∈
      𝓝 x :=
    hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds (by rw [hx1]; exact U.one_mem))
  obtain ⟨γ, -, hγ⟩ := exists_finiteDiagonal_mem_nhds K n hx hO
  refine ⟨γ * δ, u₀ * (g₁⁻¹ * (finiteDiagonal K n γ)⁻¹ * x * g₁), mul_mem hu₀ hγ, ?_⟩
  simp only [x, g₁, map_mul]
  group

open GroundTheory.Global GroundTheory.Global.IdeleGroup

variable (K)

theorem toFinite_diagonal (a : Kˣ) :
    toFinite K (IdeleGroup.diagonal K a) = FiniteAdeleRing.unitEmbedding (𝓞 K) K a :=
  Units.ext rfl

theorem comap_toFinite_sup (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔ L).comap (toFinite K) =
      (IdeleGroup.diagonal K).range ⊔ L.comap (toFinite K) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨_, ⟨a, rfl⟩, l, hl, hal⟩ := Subgroup.mem_sup.1 (Subgroup.mem_comap.1 hx)
    refine Subgroup.mem_sup.2 ⟨IdeleGroup.diagonal K a, ⟨a, rfl⟩, (IdeleGroup.diagonal K a)⁻¹ * x,
      ?_, mul_inv_cancel_left _ _⟩
    rw [Subgroup.mem_comap, map_mul, map_inv, toFinite_diagonal, ← hal, inv_mul_cancel_left]
    exact hl
  · refine sup_le ?_ (Subgroup.comap_mono le_sup_right)
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_comap, toFinite_diagonal]
    exact Subgroup.mem_sup_left ⟨a, rfl⟩

def toFiniteQuotient (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    IdeleGroup K →* (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ ((FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔ L) :=
  (QuotientGroup.mk' _).comp (toFinite K)

theorem toFiniteQuotient_surjective (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    Function.Surjective (toFiniteQuotient K L) :=
  (QuotientGroup.mk'_surjective _).comp fun x => ⟨ofFinite x, toFinite_ofFinite x⟩

theorem ker_toFiniteQuotient (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (toFiniteQuotient K L).ker = (IdeleGroup.diagonal K).range ⊔ L.comap (toFinite K) := by
  rw [toFiniteQuotient, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_toFinite_sup]

def finiteQuotientEquiv (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ ((FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔ L) ≃*
      IdeleGroup K ⧸ ((IdeleGroup.diagonal K).range ⊔ L.comap (toFinite K)) :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_toFiniteQuotient K L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toFiniteQuotient_surjective K L))).symm

def finiteQuotientEquivClassGroup :
    (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ ((FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔ finiteLevel 0) ≃*
      ClassGroup (𝓞 K) :=
  (finiteQuotientEquiv K (finiteLevel 0)).trans
    ((QuotientGroup.quotientMulEquivOfEq (by
      congr 1
      ext x
      exact (mem_standardOpenSubgroup_iff_toFinite_mem x).symm)).trans
      IdeleGroup.quotientEquivClassGroup)

variable {K}

theorem det_mem_of_forall_mem {R : Type*} [CommRing R] (T : Subring R) {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ a b, M a b ∈ T) : M.det ∈ T := by
  have : M = T.subtype.mapMatrix (Matrix.of fun a b => (⟨M a b, hM a b⟩ : T)) := by
    ext a b
    rfl
  rw [this, ← RingHom.map_det]
  exact SetLike.coe_mem _

end AdelicGLn

end

end GroundTheory.Automorphic
