module

public import Formalism.LocalToGlobal.Divisibility.ClassSum
public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV.CSD

open Formalism.DivisionValues

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem I_apply (x : Fin S.dim → K) : S.I x = ((S.basis.equivFun.symm x : S.Forms) : S.Cl → S.V) := rfl

theorem I_injective : Function.Injective S.I := by
  intro x y h
  have h' : (S.basis.equivFun.symm x : S.Forms) = S.basis.equivFun.symm y := Subtype.ext h
  exact S.basis.equivFun.symm.injective h'

theorem I_onto (f : S.Cl → S.V) : (∃ x, S.I x = f) ↔ ∀ c (γ : S.Gam c), S.ρ c γ (f c) = f c := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (S.basis.equivFun.symm x).2
  · intro h
    exact ⟨S.basis.equivFun ⟨f, h⟩, by simp [I_apply]⟩

theorem I_eq_sum (x : Fin S.dim → K) : S.I x = ∑ i, x i • (S.basis i : S.Cl → S.V) := by
  rw [I_apply, Basis.equivFun_symm_apply]
  simp

theorem csum_sum (x y : Fin S.dim → K) :
    S.csum (S.I x) (S.I y) = ∑ i, ∑ j, star (x i) * S.H i j * y j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [csum, I_eq_sum, H, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, map_sum,
    LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem isClassSum : IsClassSum S.H S.I S.pair S.wt := by
  intro x y
  have h := S.csum_sum x y
  unfold csum at h
  rw [h]
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem wt_pos (c : S.Cl) : 0 < S.wt c := Fintype.card_pos

theorem wt_dvd_DGam (c : S.Cl) : S.wt c ∣ S.DGam := Finset.dvd_lcm (Finset.mem_univ c)

theorem DGam_pos : 0 < S.DGam := by
  refine Nat.pos_of_ne_zero ?_
  unfold DGam
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨c, -, hc⟩
  exact (S.wt_pos c).ne' hc

theorem basis_eq (h : S.HasRatBasis) : S.basis = h.choose := by
  unfold basis
  exact dite_eq_left h

theorem basis_rat (h : S.HasRatBasis) (i : Fin S.dim) : S.IsRat (S.basis i : S.Cl → S.V) := by
  rw [S.basis_eq h]
  exact h.choose_spec i

end Formalism.L2.DIV.CSD
end
end

-- bundled from Formalism.LocalToGlobal.Divisibility.TuplesLemmas
section
noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling

namespace Formalism.L2.DIV

section Proved

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem mem_tupGrp {S : Set ℕ} (ξ : Chr F E L) : ξ ∈ tupGrp F E L S ↔
    ((ratId F E).range ≤ ξ.ker ∧ (∃ N : ℕ, 0 < N ∧ congN F E N ≤ ξ.ker) ∧ IsOfFinOrder ξ) ∧
      (idF F E).range ≤ ξ.ker ∧ (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ¬ GoodPl E S v → inertAt E v ≤ ξ.ker := by
  simp only [tupGrp, finChar, Subgroup.mem_inf, Subgroup.mem_iInf, mem_kills, CommGroup.mem_torsion]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

end Proved

section ProvedK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {K : Type} [Field K] [NumberField K] [StarRing K] {S : Set ℕ}

end ProvedK

theorem Tup.good {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
    {S : Set ℕ} (ξ : Tup F E L S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ Qprime (ξ : Chr F E L)) : GoodPl E S v := by
  by_contra hg
  exact hv (((mem_tupGrp (ξ : Chr F E L)).mp ξ.2).2.2.2 v hg)

def IsConjOf {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  σ ≠ AlgHom.id F E ∧ (∀ e, σ (σ e) = e) ∧ ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e

def DetInUnitaryOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), IsUnit J.det →
    ∀ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), Matrix.GeneralLinearGroup.det g ∈ U1 σ

def QprimeFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ : Chr F E L), ξ ∈ openChr F E L → (Qprime ξ).Finite

def ResCharEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) →
    ∀ P : HeightOneSpectrum (𝓞 E), ∃! χ, IsResChar ξ P χ

end Formalism.L2.DIV

end
end

