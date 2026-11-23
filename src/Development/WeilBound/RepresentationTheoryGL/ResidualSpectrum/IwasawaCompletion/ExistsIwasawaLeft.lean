module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.Bundle0001

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.C3.Fl

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N c : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N)

theorem infGL_leviEmb (m : ∀ i, GL (Fin (n i)) (Cinf E)) :
    infGL E N (leviEmb (Cinf E) (stdBlocks n h) m) = leviEmb (Ad E) (stdBlocks n h) fun i => infGL E (n i) (m i) :=
  cornerGL_leviEmb _ _ m

theorem infGL_mem_unipRad {u : GL (Fin N) (Cinf E)} (hu : u ∈ unipRad (Cinf E) (stdBlocks n h)) :
    infGL E N u ∈ unipRad (Ad E) (stdBlocks n h) :=
  cornerGL_mem_unipRad _ _ hu

theorem exists_iwasawa (g : GA E N) :
    ∃ (m : ∀ i, GA E (n i)) (u : GA E N) (k : Kinf E N) (g0 : GL (Fin N) (Af E)),
      u ∈ unipRad (Ad E) (stdBlocks n h) ∧
        g = leviEmb (Ad E) (stdBlocks n h) m * u * (infGL E N (Unitary.toUnits k) * finGL E N g0) := by
  obtain ⟨b, k, hb, hy⟩ := exists_borel_unitary (GeneralLinearGroup.map (pInf E) g)
  have hbp : b ∈ parab (Cinf E) (stdBlocks n h) := mem_parab_of_upper _ h hb
  have hlevi : ∀ (z : ∀ i, GL (Fin (n i)) (Cinf E)),
      leviEmb (Cinf E) (stdBlocks n h) z ∈ parab (Cinf E) (stdBlocks n h) := by
    intro z
    apply mem_parab_iff.2
    intro a b i j hab
    simp [leviEmb]
    simp [Matrix.blockDiagonal', hab.ne']
  let P : parab (Cinf E) (stdBlocks n h) := ⟨b, hbp⟩
  let L : parab (Cinf E) (stdBlocks n h) :=
    ⟨leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) P),
      hlevi _⟩
  let U := L⁻¹ * P
  have hu : (U : GL (Fin N) (Cinf E)) ∈ unipRad (Cinf E) (stdBlocks n h) := by
    refine Subgroup.mem_map.2 ⟨U, ?_, rfl⟩
    change leviProj (Cinf E) (stdBlocks n h) U = 1
    rw [show U = L⁻¹ * P from rfl, map_mul, map_inv]
    have : leviProj (Cinf E) (stdBlocks n h) L = leviProj (Cinf E) (stdBlocks n h) P := by
      funext a
      ext i j
      simp [L, leviProj, diagBlock, leviEmb, Matrix.blockDiagonal'_apply_eq]
    rw [this, inv_mul_cancel]
  have hbu : b = leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) P) * (U : GL (Fin N) (Cinf E)) := by
    simp [U, L, P]
  let u : GL (Fin N) (Cinf E) := U
  generalize leviProj (Cinf E) (stdBlocks n h) ⟨b, hbp⟩ = M at hbu
  change b = _ at hbu
  refine ⟨fun i => infGL E (n i) (M i), infGL E N u, k, GeneralLinearGroup.map (pFin E) g,
    infGL_mem_unipRad h hu, ?_⟩
  conv_lhs => rw [← infGL_mul_finGL g, hy, hbu]
  rw [map_mul, map_mul, infGL_leviEmb, mul_assoc]

theorem exists_iwasawa_left (g : GA E N) :
    ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GA E (n i)) (k : Kinf E N) (x : GL (Fin N) (Af E)),
      g = u * (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N x)) := by
  obtain ⟨m, u, k, x, hu, e⟩ := exists_iwasawa h g
  refine ⟨leviEmb (Ad E) (stdBlocks n h) m * u * (leviEmb (Ad E) (stdBlocks n h) m)⁻¹,
    ?_, m, k, x, ?_⟩
  · let P : parab (Ad E) (stdBlocks n h) :=
      ⟨leviEmb (Ad E) (stdBlocks n h) m, by
        apply mem_parab_iff.2
        intro a b i j hab
        simp [leviEmb]
        simp [Matrix.blockDiagonal', hab.ne']⟩
    obtain ⟨U, hU, hUeq⟩ := Subgroup.mem_map.1 hu
    rw [← hUeq]
    change ((P * U * P⁻¹ : parab (Ad E) (stdBlocks n h)) : GL (Fin N) (Ad E)) ∈ _
    refine Subgroup.mem_map.2 ⟨P * U * P⁻¹, ?_, ?_⟩
    · change leviProj (Ad E) (stdBlocks n h) (P * U * P⁻¹) = 1
      have hU' : leviProj (Ad E) (stdBlocks n h) U = 1 := hU
      simp [hU']
    · rfl
  · rw [e]
    simp only [mul_assoc, inv_mul_cancel_left]

end PositivityTheory.Rg.Rs.C3.Fl

end
