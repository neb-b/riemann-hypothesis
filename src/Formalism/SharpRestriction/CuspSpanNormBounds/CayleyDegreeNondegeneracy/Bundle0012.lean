module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0011
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FlagStabilizerMemIsotropic
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Aut

variable (D : D7) (u : D.what₂.Word) (hT : Tu D u ≠ 0) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

theorem mem_perpS_iff_mem_orth (y : (VS D).V) : y ∈ perpS (VS D) F0.X ↔ y ∈ orth (hS D) F0.X := by
  rw [Formalism.MainNotions.mem_orth_iff]
  rfl

theorem flag_stabilizer_map_isotropic (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) :
    F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
  have := hσ.2.1 D.R.rS
  rwa [partial_isotropic_top] at this

theorem flag_stabilizer_mem_isotropic (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) (x : (VS D).V) (hx : x ∈ F0.X) :
    σ x ∈ F0.X := by
  rw [← flag_stabilizer_map_isotropic D u F0 σ hσ]
  exact ⟨x, hx, rfl⟩

theorem flag_stabilizer_mem_perp (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) (y : (VS D).V)
    (hy : y ∈ perpS (VS D) F0.X) : σ y ∈ perpS (VS D) F0.X := by
  intro x hx
  rw [← flag_stabilizer_map_isotropic D u F0 σ hσ] at hx
  obtain ⟨x', hx', rfl⟩ := hx
  change (VS D).hT (σ x') (σ y) = 0
  rw [hσ.1 x' y]
  exact hy x' hx'

include he in
theorem embedding_add_smul_z_mem_perp (w : (D.sp.X 0).V) (c : D.host.E) : D.sp.iXY 0 w + c • F0.z ∈ perpS (VS D) F0.X := by
  intro x hx
  have h1 : (VS D).hT x (D.sp.iXY 0 w) = 0 :=
    Formalism.MainNotions.hT_swap_zero ((Formalism.MainNotions.mem_orth_iff _ _).1 (isotropic_le_orth_range D u F0 he hx) _ ⟨w, rfl⟩)
  have h2 : (VS D).hT x F0.z = 0 := Formalism.MainNotions.hT_zero_of_mem_X F0 F0.z_orth x hx
  rw [map_add (f := _), map_smul, h1, h2, smul_zero, add_zero]

def quotientClass (w : (D.sp.X 0).V) (c : D.host.E) : WbQ D F0 :=
  Submodule.Quotient.mk ⟨D.sp.iXY 0 w + c • F0.z, embedding_add_smul_z_mem_perp D u F0 he w c⟩

include hT hz in
theorem quotientClass_surjective (q : WbQ D F0) : ∃ w c, q = quotientClass D u F0 he w c := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨w, c, h⟩ := exists_decomp_orth_isotropic D u hT F0 he hz x.1 ((mem_perpS_iff_mem_orth D u F0 _).1 x.2)
  refine ⟨w, c, ?_⟩
  unfold quotientClass
  rw [Submodule.Quotient.eq]
  exact h

include hT hz in
theorem quotientClass_injective_left {w w' : (D.sp.X 0).V} {c c' : D.host.E} (h : quotientClass D u F0 he w c = quotientClass D u F0 he w' c') :
    w = w' := by
  unfold quotientClass at h
  rw [Submodule.Quotient.eq] at h
  have h' : D.sp.iXY 0 w + c • F0.z - (D.sp.iXY 0 w' + c' • F0.z) ∈ F0.X := h
  have hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hzW : ∀ v, (VS D).hT F0.z (D.sp.iXY 0 v) = 0 := fun v => by rw [hz]; exact z_orth_embedding D u v
  have h0 : (VS D).hT F0.z (D.sp.iXY 0 w + c • F0.z - (D.sp.iXY 0 w' + c' • F0.z)) = 0 :=
    Formalism.MainNotions.hT_swap_zero (Formalism.MainNotions.hT_zero_of_mem_X F0 F0.z_orth _ h')
  have hc : c = c' := by
    simp only [map_sub, map_add (f := _), map_smul, hzW, F0.z_norm, smul_eq_mul, zero_add] at h0
    have : (c - c') * ((Tu D u : ℕ) : D.host.E) = 0 := by linear_combination -h0
    rcases mul_eq_zero.1 this with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hT'
  subst hc
  have h2 : D.sp.iXY 0 (w - w') ∈ Wsp D ⊓ Xsp (lf D F0) := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    have e : D.sp.iXY 0 (w - w') = D.sp.iXY 0 w + c • F0.z - (D.sp.iXY 0 w' + c • F0.z) := by
      rw [map_sub]; abel
    rw [e]
    exact h'
  rw [(Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).2.1, Submodule.mem_bot] at h2
  exact sub_eq_zero.1 (embedding_W_injective D (by rw [h2, map_zero]))

def ActsAsExtendByOne (φ : WbQ D F0 → WbQ D F0) (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : Prop :=
  ∀ w c, φ (quotientClass D u F0 he w c) = quotientClass D u F0 he (γ w) c

theorem actsAsExtendByOne_of_induced (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0)
    (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hind : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X)
    (φ : WbQ D F0 → WbQ D F0)
    (hφ : ∀ (x : perpS (VS D) F0.X) (hx : σ x.1 ∈ perpS (VS D) F0.X),
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨σ x.1, hx⟩) : ActsAsExtendByOne D u F0 he φ γ := by
  intro w c
  unfold quotientClass
  rw [hφ _ (flag_stabilizer_mem_perp D u F0 σ hσ _ (embedding_add_smul_z_mem_perp D u F0 he w c)), Submodule.Quotient.eq]
  change σ (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ w) + c • F0.z) ∈ F0.X
  have e : σ (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ w) + c • F0.z) = σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) := by
    rw [map_add (f := _), map_smul, hσ.2.2]
    abel
  rw [e]
  exact hind w

theorem gmap_latticeWithZ_of_induced (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0)
    (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hind : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X)
    (Λ : LatV D) : gmap (extendByOne D γ) (latticeWithZ D F0 Λ) = latticeWithZ D F0 (gmap σ Λ) := by
  have hX := flag_stabilizer_map_isotropic D u F0 σ hσ
  have hLs := Lsub_gmap_of_isometry F0 σ hσ.1 hX Λ
  ext ⟨w, c⟩
  have e : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
  rw [isomAct_mem_gmap, e, mem_latticeWithZ_iff, mem_latticeWithZ_iff, hLs, isomAct_mem_gmap]
  have hd : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) ∈ F0.X := by
    have h1 := hind (γ.symm w)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 : σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w) ∈ F0.X := by
      rw [← Submodule.mem_map_equiv, hX]
      exact h1
    have hzs : σ.symm F0.z = F0.z := by
      rw [LinearEquiv.symm_apply_eq]
      exact hσ.2.2.symm
    have e3 : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) =
        -(σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w)) := by
      rw [map_add (f := _), map_smul, hzs, map_sub, LinearEquiv.symm_apply_apply]
      abel
    rw [e3]
    exact F0.X.neg_mem h2
  have hd' := isotropic_le_Lsub F0 Λ hd
  constructor
  · intro ha
    have := (Lsub Λ (lf D F0)).add_mem ha hd'
    simpa using this
  · intro hb
    have := (Lsub Λ (lf D F0)).sub_mem hb hd'
    simpa using this

end Aut

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTie
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_scanl_head (xs : List ℕ) (a : ℕ) : xs.scanl (· + ·) a = a :: (xs.scanl (· + ·) a).tail := by
  cases xs <;> simp [List.scanl_cons]

theorem rows_scanl_pw : ∀ (xs : List ℕ) (a : ℕ), (∀ x ∈ xs, 1 ≤ x) →
    ((xs.scanl (· + ·) a).tail).Pairwise (· < ·) ∧ ∀ y ∈ (xs.scanl (· + ·) a).tail, a < y := by
  intro xs
  induction xs with
  | nil => intro a _; simp
  | cons x xs ih =>
    intro a h
    have hx : 1 ≤ x := h x (List.mem_cons_self ..)
    obtain ⟨ih1, ih2⟩ := ih (a + x) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.scanl_cons, List.tail_cons]
    rw [rows_scanl_head xs (a + x)]
    refine ⟨List.pairwise_cons.2 ⟨fun y hy => ih2 y hy, ih1⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · omega
    · have := ih2 y hy
      omega

theorem rows_pw_ext : ∀ (l₁ l₂ : List ℕ), l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂ := by
  intro l₁ l₂ h1 h2 hm
  have hp : l₁.Perm l₂ := (List.perm_ext_iff_of_nodup (h1.imp ne_of_lt) (h2.imp ne_of_lt)).2 hm
  exact hp.eq_of_sortedLE (List.sortedLE_iff_pairwise.2 (h1.imp le_of_lt))
    (List.sortedLE_iff_pairwise.2 (h2.imp le_of_lt))

theorem rows_blockEnds_pw {i : ℕ} (p : Point ℂ i) :
    (ptBlockEnds p).Pairwise (· < ·) ∧ ∀ y ∈ ptBlockEnds p, 0 < y := by
  have h := rows_scanl_pw (p.1.map Prod.snd) 0 (by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    exact (p.2.1 b hb).2)
  exact h

section Comparison₂

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def wordPairNormRelation (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    1 ≤ ∏ τ, Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ ∧
    ∀ l, l ≤ D.R.rS + 1 → leadMinorE (termGramMatrix X t) l ≠ 0 → 1 ≤ ∏ τ, absDl D (termGramMatrix X t) l τ ^ 2

theorem rows_Dmin_ne_iff (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (τ : D.what₂.Tau) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    DminN (Y.W τ).z (Y.W τ).z' (Y.γ t τ) l ≠ 0 ↔ leadMinorE (termGramMatrix X t) l ≠ 0 := by
  rw [← norm_ne_zero_iff, d_norm_Dmin Y hrd t τ l hl]
  unfold absDl absReal
  have h0 : D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ))) ≠ 0 := (Real.rpow_pos_of_pos hrd _).ne'
  rw [mul_ne_zero_iff, norm_ne_zero_iff, map_ne_zero]
  exact ⟨fun h => h.1, fun h => ⟨h, h0⟩⟩

theorem rows_TermPtsTie_of (hrd : 0 < D.host.rdE) (hN : wordPairNormRelation X u u') : TermPtsTie X Y := by
  intro t hG hrel
  have hR : ∀ τ, RelPt D (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ) := fun τ => (Y.rel t hG hrel τ).1
  have mem_iff : ∀ τ l, l ∈ ptBlockEnds (Y.pt t τ) ↔ (1 ≤ l ∧ l ≤ D.R.rS + 1 ∧ leadMinorE (termGramMatrix X t) l ≠ 0) := by
    intro τ l
    constructor
    · intro h
      have hl := blockEnd_le (Y.pt t τ) l h
      exact ⟨(rows_blockEnds_pw (Y.pt t τ)).2 l h, hl, (rows_Dmin_ne_iff Y hrd t τ l hl).1 (cell_ne_of_mem D (hR τ) l h)⟩
    · rintro ⟨h1, hl, hne⟩
      exact cell_mem_blockEnds D (hR τ) l h1 hl ((rows_Dmin_ne_iff Y hrd t τ l hl).2 hne)
  refine ⟨fun τ => ?_, fun τ τ' => ?_, ?_, fun τ₀ l hl => ?_⟩
  · obtain ⟨_, _, hz, hz', hT, hT', _⟩ := Y.goodW τ
    exact ⟨hz, hz', hT, hT', hR τ⟩
  · exact rows_pw_ext _ _ (rows_blockEnds_pw _).1 (rows_blockEnds_pw _).1 fun x => by rw [mem_iff τ x, mem_iff τ' x]
  · rw [Finset.prod_congr rfl fun τ _ => d_Gf_eq Y hrd t τ]
    exact (hN t hG hrel).1
  · obtain ⟨_, h2, h3⟩ := (mem_iff τ₀ l).1 hl
    rw [Finset.prod_congr rfl fun τ _ => by rw [d_norm_Dmin Y hrd t τ l h2]]
    exact (hN t hG hrel).2 l h2 h3

end Comparison₂

end Formalism.MainNotions.BridgeLemma₂

end
end

