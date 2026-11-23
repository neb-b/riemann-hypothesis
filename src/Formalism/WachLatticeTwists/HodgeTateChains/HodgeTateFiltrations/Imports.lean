module

public import Formalism.WachLatticeTwists.HodgeTateChains.InvariantsCohomologyData
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.InverseOperatorFromInjectivity

@[expose] public section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

theorem piece : StatPiece := by
  intro ℓ _ w m hm h2 hw U i A P ⟨hS, ⟨hIR1, hIR2⟩, hT4, ⟨_, hT3⟩, htf, hHT⟩ y ⟨k, hk⟩
  have hkill : aeval P.gm ((X - 1) * Rpoly ℓ w U i) = 0 := by
    obtain ⟨q, hq⟩ := (htpoly ℓ w U i).1
    rw [hq, map_mul, hHT, zero_mul]
  have h1 : P.res ((ℓ : ℤ_[ℓ]) • P.lam y) = 0 := by rw [map_smul]; exact hT4 _
  obtain ⟨a, x, hax⟩ := (hIR1 _).1 h1
  have h3 : P.infm (((ℓ : ℤ_[ℓ]) ^ k) • a) + P.infX (((ℓ : ℤ_[ℓ]) ^ k) • x) = 0 := by
    rw [map_smul, map_smul, ← smul_add, ← hax, smul_comm, ← map_smul, hk, map_zero, smul_zero]
  obtain ⟨⟨a', ha'⟩, _⟩ := (hIR2 _ _).1 h3
  obtain ⟨a'', ha''⟩ := eigen ℓ w m hm h2 hw U i P.Wm P.gm htf hkill k a a' ha'
  obtain ⟨x'', hx''⟩ := hT3 x
  have h4 : P.infm (((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i))) • a) + P.infX (((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i))) • x) = 0 := by
    apply (hIR2 _ _).2
    constructor
    · refine ⟨((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i) - rI ℓ m U i)) • a'', ?_⟩
      rw [map_smul, ← smul_sub, ← ha'', smul_smul, ← pow_add, Nat.sub_add_cancel (le_max_right _ _)]
    · refine ⟨((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i) - 1)) • x'', ?_⟩
      rw [map_smul, ← smul_sub, ← hx'', smul_smul, ← pow_succ, Nat.sub_add_cancel (le_max_left _ _)]
  have h5 : ((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i) + 1)) • P.lam y = 0 := by
    rw [pow_succ, mul_smul, hax, smul_add, ← map_smul, ← map_smul]; exact h4
  have h6 := congrArg P.io h5
  rw [map_smul, hS, map_zero, smul_smul, ← pow_succ] at h6
  have h7 : 2 + max 1 (rI ℓ m U i) = max 1 (rI ℓ m U i) + 1 + 1 := by ring
  rw [h7]; exact h6

theorem h0 : InvariantsKilledByPower := by
  intro ℓ _ w m hm h2 hw U h0U hne D hP hUn hFl hLES ⟨hInv1, hInv2⟩ x
  have hA := piece ℓ w m hm h2 hw U 0 D.A D.piece hP
  have hr : rI ℓ m U 0 = ∑ u ∈ U, (m + padicValInt ℓ u) := by
    unfold rI; rw [Finset.erase_eq_of_notMem h0U]; simp
  have hr1 : 1 ≤ rI ℓ m U 0 := by
    rw [hr]
    obtain ⟨u, hu⟩ := hne
    calc 1 ≤ m + padicValInt ℓ u := by omega
      _ ≤ _ := Finset.single_le_sum (f := fun u => m + padicValInt ℓ u) (fun _ _ => Nat.zero_le _) hu
  have hc : 2 + max 1 (rI ℓ m U 0) = c0 ℓ m U := by unfold c0; rw [max_eq_right hr1, hr]
  rw [hc] at hA
  obtain ⟨_, _, _, ⟨hT3inj, _⟩, htf, hHT⟩ := hP
  have hW0 : ∀ z : D.H0WeightInvariants, z = 0 := fun z =>
    hInv1 z (eigenInj ℓ w m hm h2 hw U 0 h0U D.piece.Wm D.piece.gm htf hHT _ (hInv2 z).1)
      (hT3inj _ (hInv2 z).2)
  obtain ⟨r, hr'⟩ := hUn x
  let x' : Submodule.torsionBy ℤ_[ℓ] D.M ((ℓ : ℤ_[ℓ]) ^ r) :=
    ⟨x, by rw [Submodule.mem_torsionBy_iff]; exact hr'⟩
  have hx0 : ((ℓ : ℤ_[ℓ]) ^ r) • x' = 0 := Subtype.ext hr'
  have h1 : ((ℓ : ℤ_[ℓ]) ^ c0 ℓ m U) • D.dl r (D.emb r x') = 0 :=
    hA _ ⟨r, by rw [← map_smul, ← map_smul, hx0, map_zero, map_zero]⟩
  have h2' : D.dl r (D.emb r (((ℓ : ℤ_[ℓ]) ^ c0 ℓ m U) • x')) = 0 := by rw [map_smul, map_smul]; exact h1
  obtain ⟨z, hz⟩ := (hLES r _).1 h2'
  rw [hW0 z, map_zero] at hz
  have h3 : ((ℓ : ℤ_[ℓ]) ^ c0 ℓ m U) • x' = 0 := hFl r (by rw [← hz, map_zero])
  exact congrArg Subtype.val h3

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
