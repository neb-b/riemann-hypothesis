module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.AtomEqZero
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.QIterSurjective
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.ExistsOrthOfFinset
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0285
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Twist

theorem twist_irr {G D : Type} [Group G] [AddCommGroup D] [Module ℂ D] (ρ : Representation ℂ G D) (χ : G →* ℂˣ)
    (h : ρ.IsIrreducible) : (twist ρ χ).IsIrreducible := by
  let f : Subrepresentation ρ ≃o Subrepresentation (twist ρ χ) :=
    { toFun := fun W => ⟨W.toSubmodule, fun g v hv => by
        show ((χ g : ℂˣ) : ℂ) • ρ g v ∈ W.toSubmodule
        exact W.toSubmodule.smul_mem _ (W.apply_mem_toSubmodule g hv)⟩
      invFun := fun W => ⟨W.toSubmodule, fun g v hv => by
        have h1 := W.apply_mem_toSubmodule g hv
        have h2 : ρ g v = (((χ g)⁻¹ : ℂˣ) : ℂ) • (twist ρ χ g v) := by
          show ρ g v = (((χ g)⁻¹ : ℂˣ) : ℂ) • (((χ g : ℂˣ) : ℂ) • ρ g v)
          rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
        rw [h2]
        exact W.toSubmodule.smul_mem _ h1⟩
      left_inv := fun W => rfl
      right_inv := fun W => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff f).1 h

end Twist

section Casts

theorem sub_iff_twKer (ψ : AddChar k Circle) (n j : ℕ) (π : GRep k (n + (j + 1))) :
    Subsingleton (derivB ψ (j + 1) π).V ↔
      twKer π.ρ (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) = ⊤ := by
  obtain ⟨q, hqs, hqk, -⟩ := derDict ψ n j π.ρ
  rw [← hqk]
  constructor
  · intro hs
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]
    exact @Subsingleton.elim _ hs _ _
  · intro hk
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, rfl⟩ := hqs x
    obtain ⟨b, rfl⟩ := hqs y
    have ha : a ∈ LinearMap.ker q := hk ▸ Submodule.mem_top
    have hb : b ∈ LinearMap.ker q := hk ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at ha hb
    exact ha.trans hb.symm

theorem cast_twKer (ψ : AddChar k Circle) {a b : ℕ} (e : a = b) (π : GRep k a) (m : ℕ) :
    twKer (π.cast e).ρ (derUnip k b m) (derChar k ψ b m) = ⊤ ↔ twKer π.ρ (derUnip k a m) (derChar k ψ a m) = ⊤ := by
  subst e
  rfl

end Casts

section Desc

variable (hUD : UDens k) (hUA : UAtom k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
  (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

theorem chain_psd (hB : IsInvForm π B) : ∀ d, d + 1 ≤ N → IsPsd (chain hUD hψc hψ1 π hs B d)
  | 0, _ => isPsd_of_inv π B hB
  | d + 1, hd => by
    have hd2 : d + 2 ≤ N := by omega
    have hL := chain_lvl hUD hψc hψ1 π hs B hB d hd2
    exact (chain_succ hUD hψc hψ1 π hs B d hd2 hL).2.1

theorem chain_kills (hB : IsInvForm π B) : ∀ d, d + 1 ≤ N → Kills ψ π (N - d) (chain hUD hψc hψ1 π hs B d) := by
  have killsZero : Kills ψ π N (chain hUD hψc hψ1 π hs B 0) := by
    intro v hv w
    rw [twKer_derUnip_self ψ π] at hv
    rw [(Submodule.mem_bot ℂ).1 hv]
    simp
  intro d hd
  cases d with
  | zero => exact killsZero
  | succ d =>
    have hd2 : d + 2 ≤ N := by omega
    have hL := chain_lvl hUD hψc hψ1 π hs B hB d hd2
    exact kills_congr (by omega) (chain_succ hUD hψc hψ1 π hs B d hd2 hL).2.2.1


include hUA in
theorem twisted_kernel_forms_nonvanishing (hUS : USplit k) (hB : IsInvForm π B) :
    ∀ e d, d + e + 1 = N → (∃ v, chain hUD hψc hψ1 π hs B d v v ≠ 0) →
      ∃ n', n' + d + 1 ≤ N ∧ twKer π (derUnip k N n') (derChar k ψ N n') ≠ ⊤ := by
  intro e
  induction e with
  | zero =>
    rintro d hde ⟨v, hv⟩
    refine ⟨0, by omega, fun htop => hv ?_⟩
    have hK := chain_kills hUD hψc hψ1 π hs B hB d (by omega)
    have e1 : N - d = 1 := by omega
    rw [e1] at hK
    refine hK v ?_ v
    have hle : twKer π (derUnip k N 0) (derChar k ψ N 0) ≤ twKer π (derUnip k N 1) (lvlChar k ψ N 1) :=
      twKer_mono π _ _ (le_inf inf_le_left (inf_le_left.trans (unipB_le_colFix_one N))) fun u => rfl
    exact hle (htop ▸ Submodule.mem_top)
  | succ e ih =>
    rintro d hde ⟨v, hv⟩
    have hd2 : d + 2 ≤ N := by omega
    by_cases h0 : ∀ w, chain hUD hψc hψ1 π hs B (d + 1) w w = 0
    · have hA := atom_eq_self hUD hUA hψc hψ1 π hs B hUS hB d hd2 h0
      have hL := chain_lvl hUD hψc hψ1 π hs B hB d hd2
      have hK := (atom_spec hUD hUA hψc hψ1 π hs B d hd2 hL).2.2.2.1
      refine ⟨N - 2 - d + 1, by omega, fun htop => hv ?_⟩
      have hmem : v ∈ DerKer k ψ π (N - 2 - d) := by
        unfold DerKer
        rw [htop]
        exact Submodule.mem_top
      have := hK v hmem v
      rwa [hA] at this
    · have hnext : ∃ w, chain hUD hψc hψ1 π hs B (d + 1) w w ≠ 0 := not_forall.mp h0
      obtain ⟨n', hn', hne⟩ := ih (d + 1) (by omega) hnext
      exact ⟨n', by omega, hne⟩

theorem chain_ne_of (hB : IsInvForm π B) (d n' : ℕ) (hd : d + 1 ≤ N) (hn' : n' + d < N)
    (hne : twKer π (derUnip k N n') (derChar k ψ N n') ≠ ⊤) : ∃ v, chain hUD hψc hψ1 π hs B d v v ≠ 0 := by
  have radical : ∀ j, j + 1 ≤ N → ∀ v, chain hUD hψc hψ1 π hs B j v v = 0 →
      v ∈ twKer π (derUnip k N (N - j)) (lvlChar k ψ N (N - j)) := by
    intro j
    induction j with
    | zero =>
      intro _ v hv
      rw [chain_zero] at hv
      by_cases h : v = 0
      · rw [h]
        exact zero_mem _
      · have hpos := hB.2.1 v h
        simp [hv] at hpos
    | succ j ih =>
      intro hj v hv
      have hj2 : j + 2 ≤ N := by omega
      have hL := chain_lvl hUD hψc hψ1 π hs B hB j hj2
      obtain ⟨-, -, -, -, hR⟩ := chain_succ hUD hψc hψ1 π hs B j hj2 hL
      have hmem := hR v hv
      have e : N - 2 - j + 1 = N - (j + 1) := by omega
      rw [e] at hmem
      suffices hle : LinearMap.ker (chain hUD hψc hψ1 π hs B j) ≤
          twKer π (derUnip k N (N - (j + 1))) (lvlChar k ψ N (N - (j + 1))) from
        (sup_le le_rfl hle) hmem
      intro x hx
      rw [LinearMap.mem_ker] at hx
      have hx0 : chain hUD hψc hψ1 π hs B j x x = 0 := by simp [hx]
      have hK := ih (by omega) x hx0
      rw [lvlChar_def] at hK ⊢
      exact twKer_derUnip_le ψ π (a := N - j) (b := N - (j + 1))
        (x := N - j - 1) (y := N - (j + 1) - 1) (by omega) (by omega) (by omega) hK
  by_contra hall
  apply hne
  rw [eq_top_iff]
  intro v _
  have hv := radical d hd v (not_exists_not.mp hall v)
  rw [lvlChar_def] at hv
  rw [derChar_def]
  exact twKer_derUnip_le ψ π (a := N - d) (b := n') (x := N - d - 1) (y := n') (by omega) (by omega) (by omega) hv

end Desc

end PositivityTheory.RgUd.Form.U.Asm
