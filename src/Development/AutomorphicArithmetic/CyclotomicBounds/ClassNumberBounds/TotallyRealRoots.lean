module

public import Mathlib

@[expose] public section

namespace KStar

section Def

variable {R : Type*} [CommRing R]

noncomputable def nuStar (p : R) (U : Set R) (tr : ℕ) : ℕ∞ :=
  sInf ((fun u => emultiplicity p (u ^ tr - 1)) '' U)

theorem le_nuStar_iff (p : R) (U : Set R) (tr n : ℕ) :
    (n : ℕ∞) ≤ nuStar p U tr ↔ ∀ u ∈ U, p ^ n ∣ u ^ tr - 1 := by
  unfold nuStar
  rw [le_sInf_iff, Set.forall_mem_image]
  exact forall₂_congr fun u _ => pow_dvd_iff_le_emultiplicity.symm

theorem exists_eq_nuStar {p : R} {U : Set R} (hU : U.Nonempty) (tr : ℕ) :
    ∃ u ∈ U, emultiplicity p (u ^ tr - 1) = nuStar p U tr := by
  have h := csInf_mem (hU.image (fun u => emultiplicity p (u ^ tr - 1)))
  obtain ⟨u, hu, e⟩ := h
  exact ⟨u, hu, e⟩

theorem exists_exact_of_nuStar_eq {p : R} {U : Set R} {tr ν : ℕ} (h : nuStar p U tr = ν) :
    ∃ u ∈ U, p ^ ν ∣ u ^ tr - 1 ∧ ¬ p ^ (ν + 1) ∣ u ^ tr - 1 := by
  rcases U.eq_empty_or_nonempty with hU | hU
  · subst hU
    simp [nuStar] at h
  obtain ⟨u, hu, e⟩ := exists_eq_nuStar hU tr
  rw [h] at e
  refine ⟨u, hu, pow_dvd_iff_le_emultiplicity.mpr e.ge, fun hd => ?_⟩
  have := pow_dvd_iff_le_emultiplicity.mp hd
  rw [e] at this
  norm_cast at this
  omega

theorem eq_nuStar_of_forall {p : R} {U : Set R} {tr : ℕ} (m : ℕ∞)
    (hm : ∀ n : ℕ, (n : ℕ∞) ≤ m ↔ ∀ u ∈ U, p ^ n ∣ u ^ tr - 1) : m = nuStar p U tr := by
  refine le_antisymm ?_ ?_
  · refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
    exact (le_nuStar_iff p U tr n).mpr ((hm n).mp hn)
  · refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
    exact (hm n).mpr ((le_nuStar_iff p U tr n).mp hn)

end Def

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

end Domain

section Int

end Int

section Inhabitant

end Inhabitant

end KStar
