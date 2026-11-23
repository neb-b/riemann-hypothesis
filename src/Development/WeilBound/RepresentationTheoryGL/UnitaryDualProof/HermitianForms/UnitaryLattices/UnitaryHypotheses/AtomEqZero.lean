module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.Bundle0001

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blkAt_self (N : ℕ) (h : N ≤ N) (g : GL (Fin N) k) : blkAt k N N h g = g := by
  ext a b
  rw [blkAt_apply]
  simp [a.2, b.2]


open Classical in
def atom (hUD : UDens k) (hUA : UAtom k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (d : ℕ) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  if h : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) then
    Classical.choose (hUA ψ hψc hψ1 (N - 2 - d) N (by obtain ⟨hN, -⟩ := h; omega) V π hs (d : ℝ)
      (chain hUD hψc hψ1 π hs B d) h.2)
  else 0

variable (hUD : UDens k) (hUA : UAtom k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
  (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

theorem atom_spec (d : ℕ) (hN : d + 2 ≤ N)
    (hL : Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d)) :
    IsAtom (by omega : N - 2 - d + 2 ≤ N) π (chain hUD hψc hψ1 π hs B d) (atom hUD hUA hψc hψ1 π hs B d) ∧
      IsPsd (atom hUD hUA hψc hψ1 π hs B d) ∧
      (∀ v, (atom hUD hUA hψc hψ1 π hs B d v v).re ≤ (chain hUD hψc hψ1 π hs B d v v).re) ∧
      (∀ v ∈ DerKer k ψ π (N - 2 - d), ∀ w, atom hUD hUA hψc hψ1 π hs B d v w = 0) ∧
      GLEq k π (N - 2 - d) (by omega) (d : ℝ) (atom hUD hUA hψc hψ1 π hs B d) ∧
      MirEq π (N - 2 - d + 1) (by omega) (d : ℝ) (atom hUD hUA hψc hψ1 π hs B d) := by
  have hh : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) := ⟨hN, hL⟩
  have e : atom hUD hUA hψc hψ1 π hs B d = Classical.choose (hUA ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ)
      (chain hUD hψc hψ1 π hs B d) hL) := by
    rw [atom, dite_eq_left hh]
  rw [e]
  exact Classical.choose_spec (hUA ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ) (chain hUD hψc hψ1 π hs B d) hL)

theorem lift (hUL : ULift k) (hTB : ThmB k) (hirr : π.IsIrreducible) (hB : IsInvForm π B) :
    ∀ d (hd : d + 1 ≤ N) (C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), IsPsd C → Kills ψ π (N - d) C →
      MirEq π (N - d - 1) (by omega) (d : ℝ) C →
      (∀ v, (C v v).re ≤ (chain hUD hψc hψ1 π hs B d v v).re) →
      ∃ c : ℂ, ∀ v w, C v w = c * chain hUD hψc hψ1 π hs B d v w := by
  have level : ∀ j (hj : j + 2 ≤ N),
      Lvl k ψ π (N - 2 - j) (by omega) (j : ℝ) (chain hUD hψc hψ1 π hs B j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [chain_zero]
      refine ⟨isPsd_of_inv π B hB, kills_congr (a := N) (by omega) ?_, ?_⟩
      · intro v hv w
        rw [twKer_derUnip_self ψ π] at hv
        rw [(Submodule.mem_bot ℂ).1 hv]
        simp
      · intro p _ v w
        simp [hB.2.2]
    | succ j ih =>
      intro hj
      obtain ⟨-, hP, hK, hM, -⟩ := chain_succ hUD hψc hψ1 π hs B j (by omega) (ih (by omega))
      exact ⟨hP, kills_congr (by omega) hK, mirEq_congr (by omega) (by push_cast; ring) hM⟩
  intro d
  induction d with
  | zero =>
    intro hd C _ _ hC3 _
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hM : MirEq π n (by omega) ((0 : ℕ) : ℝ) C := mirEq_congr (by omega) rfl hC3
    rw [chain_zero]
    refine hTB n V π hs hirr B hB C fun p hp v w => ?_
    have := hM p hp v w
    rw [blkAt_self] at this
    simpa using this
  | succ d ih =>
    intro _hd C hC1 hC2 hC3 hC4
    have hL := level d (by omega)
    obtain ⟨hD, -⟩ := chain_succ hUD hψc hψ1 π hs B d (by omega) hL
    obtain ⟨I, hIL, hIle, hID, -⟩ := hUL ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ)
      (chain hUD hψc hψ1 π hs B d) (chain hUD hψc hψ1 π hs B (d + 1)) C (lat0 k (N - 2 - d)) hL (isLattice_standard_lattice _) hD hC1
      (kills_congr (by omega) hC2) (mirEq_congr (by omega) (by push_cast; ring) hC3) hC4
    obtain ⟨c, hc⟩ := ih (by omega) I hIL.1 (kills_congr (by omega) hIL.2.1)
      (mirEq_congr (by omega) rfl hIL.2.2) hIle
    exact ⟨c, isDens_smul hD hID c hc⟩

theorem chain_rad (hB : IsInvForm π B) (d : ℕ) (hd : d + 1 ≤ N) :
    ∀ v, chain hUD hψc hψ1 π hs B d v v = 0 →
      v ∈ twKer π (derUnip k N (N - d)) (lvlChar k ψ N (N - d)) := by
  revert d
  have level : ∀ j (hj : j + 2 ≤ N),
      Lvl k ψ π (N - 2 - j) (by omega) (j : ℝ) (chain hUD hψc hψ1 π hs B j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [chain_zero]
      refine ⟨isPsd_of_inv π B hB, kills_congr (a := N) (by omega) ?_, ?_⟩
      · intro v hv w
        rw [twKer_derUnip_self ψ π] at hv
        rw [(Submodule.mem_bot ℂ).1 hv]
        simp
      · intro p _ v w
        simp [hB.2.2]
    | succ j ih =>
      intro hj
      obtain ⟨-, hP, hK, hM, -⟩ := chain_succ hUD hψc hψ1 π hs B j (by omega) (ih (by omega))
      exact ⟨hP, kills_congr (by omega) hK, mirEq_congr (by omega) (by push_cast; ring) hM⟩
  intro d
  induction d with
  | zero =>
    intro _ v hv
    have : v = 0 := by
      by_contra hne
      have := hB.2.1 v hne
      rw [chain_zero] at hv
      rw [hv] at this
      simp at this
    rw [this]
    exact zero_mem _
  | succ d ih =>
    intro hd v hv
    have hL := level d (by omega)
    obtain ⟨-, -, -, -, hR⟩ := chain_succ hUD hψc hψ1 π hs B d (by omega) hL
    have hmem := hR v hv
    have e : N - 2 - d + 1 = N - (d + 1) := by omega
    rw [e] at hmem
    suffices hle : LinearMap.ker (chain hUD hψc hψ1 π hs B d) ≤
        twKer π (derUnip k N (N - (d + 1))) (lvlChar k ψ N (N - (d + 1))) from (sup_le le_rfl hle) hmem
    intro x hx
    have hx0 : chain hUD hψc hψ1 π hs B d x x = 0 := by
      rw [LinearMap.mem_ker] at hx
      rw [hx]
      rfl
    have hK := ih (by omega) x hx0
    rw [lvlChar_def] at hK ⊢
    exact twKer_derUnip_le ψ π (a := N - d) (b := N - (d + 1)) (x := N - d - 1) (y := N - (d + 1) - 1)
      (by omega) (by omega) (by omega) hK

theorem atom_prop (hUL : ULift k) (hTB : ThmB k) (hirr : π.IsIrreducible) (hB : IsInvForm π B) (d : ℕ)
    (hd : d + 2 ≤ N) : ∃ c : ℂ, ∀ v w, atom hUD hUA hψc hψ1 π hs B d v w = c * chain hUD hψc hψ1 π hs B d v w := by
  have level : ∀ j (hj : j + 2 ≤ N),
      Lvl k ψ π (N - 2 - j) (by omega) (j : ℝ) (chain hUD hψc hψ1 π hs B j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [chain_zero]
      refine ⟨isPsd_of_inv π B hB, kills_congr (a := N) (by omega) ?_, ?_⟩
      · intro v hv w
        rw [twKer_derUnip_self ψ π] at hv
        rw [(Submodule.mem_bot ℂ).1 hv]
        simp
      · intro p _ v w
        simp [hB.2.2]
    | succ j ih =>
      intro hj
      obtain ⟨-, hP, hK, hM, -⟩ := chain_succ hUD hψc hψ1 π hs B j (by omega) (ih (by omega))
      exact ⟨hP, kills_congr (by omega) hK, mirEq_congr (by omega) (by push_cast; ring) hM⟩
  have hL := level d hd
  obtain ⟨-, hA1, hA2, hA3, -, hA5⟩ := atom_spec hUD hUA hψc hψ1 π hs B d hd hL
  refine lift hUD hψc hψ1 π hs B hUL hTB hirr hB d (by omega) _ hA1 ?_ (mirEq_congr (by omega) rfl hA5) hA2
  intro v hv w
  refine hA3 v ?_ w
  simp only [DerKer]
  rw [lvlChar_def] at hv
  rw [derChar_def]
  exact twKer_derUnip_le ψ π (a := N - d) (b := N - 2 - d + 1) (x := N - d - 1) (y := N - 2 - d + 1)
    (by omega) (by omega) (by omega) hv

theorem atom_eq_zero (hUS : USplit k) (hUL : ULift k) (hTB : ThmB k) (hirr : π.IsIrreducible) (hB : IsInvForm π B)
    (d : ℕ) (hd : d + 2 ≤ N) (hne : ∃ v, chain hUD hψc hψ1 π hs B (d + 1) v v ≠ 0) :
    ∀ v w, atom hUD hUA hψc hψ1 π hs B d v w = 0 := by
  have level : ∀ j (hj : j + 2 ≤ N),
      Lvl k ψ π (N - 2 - j) (by omega) (j : ℝ) (chain hUD hψc hψ1 π hs B j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [chain_zero]
      refine ⟨isPsd_of_inv π B hB, kills_congr (a := N) (by omega) ?_, ?_⟩
      · intro v hv w
        rw [twKer_derUnip_self ψ π] at hv
        rw [(Submodule.mem_bot ℂ).1 hv]
        simp
      · intro p _ v w
        simp [hB.2.2]
    | succ j ih =>
      intro hj
      obtain ⟨-, hP, hK, hM, -⟩ := chain_succ hUD hψc hψ1 π hs B j (by omega) (ih (by omega))
      exact ⟨hP, kills_congr (by omega) hK, mirEq_congr (by omega) (by push_cast; ring) hM⟩
  have hL := level d hd
  obtain ⟨hAt, -⟩ := atom_spec hUD hUA hψc hψ1 π hs B d hd hL
  obtain ⟨hD, -⟩ := chain_succ hUD hψc hψ1 π hs B d hd hL
  obtain ⟨c, hc⟩ := atom_prop hUD hUA hψc hψ1 π hs B hUL hTB hirr hB d hd
  have h0 := (hUS ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ) (chain hUD hψc hψ1 π hs B d)
    (atom hUD hUA hψc hψ1 π hs B d) (chain hUD hψc hψ1 π hs B (d + 1)) (lat0 k (N - 2 - d)) hL (isLattice_standard_lattice _)
    hAt hD).2 c hc hne
  intro v w
  rw [hc, h0, zero_mul]

theorem atom_eq_self (hUS : USplit k) (hB : IsInvForm π B) (d : ℕ) (hd : d + 2 ≤ N)
    (h0 : ∀ v, chain hUD hψc hψ1 π hs B (d + 1) v v = 0) :
    atom hUD hUA hψc hψ1 π hs B d = chain hUD hψc hψ1 π hs B d := by
  have level : ∀ j (hj : j + 2 ≤ N),
      Lvl k ψ π (N - 2 - j) (by omega) (j : ℝ) (chain hUD hψc hψ1 π hs B j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [chain_zero]
      refine ⟨isPsd_of_inv π B hB, kills_congr (a := N) (by omega) ?_, ?_⟩
      · intro v hv w
        rw [twKer_derUnip_self ψ π] at hv
        rw [(Submodule.mem_bot ℂ).1 hv]
        simp
      · intro p _ v w
        simp [hB.2.2]
    | succ j ih =>
      intro hj
      obtain ⟨-, hP, hK, hM, -⟩ := chain_succ hUD hψc hψ1 π hs B j (by omega) (ih (by omega))
      exact ⟨hP, kills_congr (by omega) hK, mirEq_congr (by omega) (by push_cast; ring) hM⟩
  have hL := level d hd
  obtain ⟨hAt, -⟩ := atom_spec hUD hUA hψc hψ1 π hs B d hd hL
  obtain ⟨hD, -⟩ := chain_succ hUD hψc hψ1 π hs B d hd hL
  exact (hUS ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ) (chain hUD hψc hψ1 π hs B d)
    (atom hUD hUA hψc hψ1 π hs B d) (chain hUD hψc hψ1 π hs B (d + 1)) (lat0 k (N - 2 - d)) hL (isLattice_standard_lattice _)
    hAt hD).1 h0

end PositivityTheory.RgUd.Form.U.Asm
