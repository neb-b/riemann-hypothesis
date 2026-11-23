module

public import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchOfCoordinatesAndCount
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
public import Formalism.LocalToGlobal.GlobalTheory.GL6.WeylLengthDiagonalUnitUniformiser
public import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.ValuationDetBasisChangeZero
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PKerAtP
public import Formalism.LocalToGlobal.UnitaryNorms.UnramT

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.DuCount
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open MvPolynomial

section Rank

theorem finrank_weylZ {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) :
    Module.finrank ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r r le_rfl ν) = Nat.card (Formalism.GradedWeylDivisibility.ssIdx r r ν) := by
  classical
  obtain ⟨ι, hι, b, -, -, -⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.weyl_homogeneous_basis (ν := ν) (hn := le_rfl) hν
  let φ : ℤ →+* ℚ := Int.castRingHom ℚ
  let v : ι → MvPolynomial (Fin r × Fin r) ℚ := fun i => MvPolynomial.map φ (b i : MvPolynomial (Fin r × Fin r) ℤ)
  have hbli : LinearIndependent ℤ (fun i => (b i : MvPolynomial (Fin r × Fin r) ℤ)) :=
    b.linearIndependent.map' (Formalism.GradedWeylDivisibility.weyl ℤ r r le_rfl ν).subtype (Submodule.ker_subtype _)
  have hinj : Function.Injective (MvPolynomial.map φ : MvPolynomial (Fin r × Fin r) ℤ → MvPolynomial (Fin r × Fin r) ℚ) :=
    MvPolynomial.map_injective _ (RingHom.injective_int φ)
  have hvZ : LinearIndependent ℤ v :=
    hbli.map' (MvPolynomial.map φ : MvPolynomial (Fin r × Fin r) ℤ →+* MvPolynomial (Fin r × Fin r) ℚ).toAddMonoidHom.toIntLinearMap
      (LinearMap.ker_eq_bot.2 hinj)
  have hvQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hvZ
  have hspan : Submodule.span ℚ (Set.range v) = Formalism.GradedWeylDivisibility.weyl ℚ r r le_rfl ν := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Formalism.L2.G.Model.sw_weyl_map φ le_rfl ν _ (b i).2
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨w, rfl⟩
      have hmem : Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ (le_rfl : r ≤ r) ν) ∈ Formalism.GradedWeylDivisibility.weyl ℤ r r le_rfl ν :=
        Submodule.subset_span ⟨w, rfl⟩
      have hx_eq : Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ (le_rfl : r ≤ r) ν) =
          ∑ i, b.repr ⟨_, hmem⟩ i • (b i : MvPolynomial (Fin r × Fin r) ℤ) := by
        have h := congrArg Subtype.val (b.sum_repr ⟨_, hmem⟩)
        rw [Submodule.coe_sum] at h
        simp only [Submodule.coe_smul] at h
        exact h.symm
      show Formalism.GradedWeylDivisibility.applyWord ℚ w (Formalism.GradedWeylDivisibility.hw ℚ (le_rfl : r ≤ r) ν) ∈ Submodule.span ℚ (Set.range v)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Formalism.GradedWeylDivisibility.lclosedeq_hw_map φ, Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, hx_eq, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul]
      exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := v) i) : v i ∈ Submodule.span ℚ (Set.range v)) _
  obtain ⟨b', hb', -⟩ := Formalism.GradedWeylDivisibility.sSBasis ℚ r r ν
  haveI : Fintype (Formalism.GradedWeylDivisibility.ssIdx r r ν) := (Formalism.GradedWeylDivisibility.sSIdxFinite r r ν).fintype
  have h1 := finrank_span_eq_card hvQ
  have h2 := finrank_span_eq_card hb'.1
  rw [hspan, Formalism.L2.G.Model.sw_weyl_eq ℚ r r le_rfl ν hν, ← hb'.2.1] at h1
  rw [Module.finrank_eq_card_basis b, Nat.card_eq_fintype_card, ← h1, h2]

theorem finrank_delSqZ {N : ℕ} (lam : Formalism.BasicNotions.DomWeight N) :
    Module.finrank ℤ (Formalism.BasicNotions.delSq ℤ N lam) = Nat.card (Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) :=
  finrank_weylZ lam.natW (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_natW_anti lam)

end Rank

section Mu0

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.Forms Formalism.BasicNotions

theorem finrank_forms_level_zero {D : D7} {u : D.what₂.Word} (T : Forms0 D u) (hst : (D.mem u).C.StabZero) :
    Module.finrank ℂ (D.mem u).A.Mu0 = Fintype.card ((D.mem u).C.cls 0) *
      ∏ τ, Nat.card (Formalism.GradedWeylDivisibility.ssIdx (D.R.N 0) (D.R.N 0) ((D.fm u).lam 0 τ).natW) := by
  classical
  let e : ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) ≃ₗ[ℂ] ((D.mem u).C.cls 0 → _ → ℂ) :=
    LinearEquiv.piCongrRight fun _ => LinearEquiv.funCongrLeft ℂ ℂ T.val0.eY.symm
  have hfi := Formalism.MainNotions.Ext.Lw.fiC_eq_pi T.cls0.lev (Formalism.L2.Forms.embT D) ((D.fm u).lam 0) T.cls0.y T.cls0.y_bij
    (fun c γ hγ => by
      haveI := hst c
      obtain ⟨s, hs⟩ := (T.cls0.stabI_range c γ).2 hγ
      rw [← hs, Subsingleton.elim s 1, map_one])
  have hmap : (D.mem u).A.Mu0.map (e : _ →ₗ[ℂ] _) = FiC T.cls0.lev (Formalism.L2.Forms.embT D) ((D.fm u).lam 0) T.cls0.y := by
    ext ψ
    rw [Submodule.mem_map_equiv, Formalism.L2.Forms.Mu0_iff T.val0]
    have hψ : (fun c z => e.symm ψ c (T.val0.eY.symm z)) = ψ := by
      funext c z
      simp [e]
    rw [hψ]
  rw [(e.submoduleMap (D.mem u).A.Mu0).finrank_eq, hmap, hfi, Formalism.MainNotions.Ext.Lw.finrank_pi_const,
    Formalism.MainNotions.Ext.Lw.finrank_valC]

end Mu0

theorem duCount_holds : ∀ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word), Formalism.L2.Forms.Forms0 D u → Formalism.MainNotions.product_first_zeroth_parts.admS D u →
    DuCount D u := by
  intro D u T hadm
  unfold DuCount
  have h1 := finrank_forms_level_zero T hadm
  have h2 : ∀ τ, Module.finrank ℤ (Formalism.BasicNotions.delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) =
      Nat.card (Formalism.GradedWeylDivisibility.ssIdx (D.R.N 0) (D.R.N 0) ((D.fm u).lam 0 τ).natW) := fun τ => finrank_delSqZ _
  simp_rw [h2]
  rw [← h1]
  first
    | rfl
    | (unfold Formalism.BasicNotions.D7.duS; rfl)
    | simp [Formalism.BasicNotions.D7.duS]

end Formalism.L2.GlobalTheoryTheory.LemB

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchCoordinatesOfSurjectivity
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB NumberField Classical

theorem locBases {D : D7} {u : D.what₂.Word} (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    (∃ B : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B) ∧
    ∀ v, ∃ B' : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Lk A i hi v c : Set _) B' := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have hL := bwB_clsCrd_lat D u i hi c
  have hFull : Submodule.IsFullLattice D.host.E (clsCrd D u i hi c) :=
    { toIsLattice := hL, span_eq_top := (tld_isLat i hi c).2 }
  obtain ⟨d, hd, hle⟩ := dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (bwB_gramN_det D i hi) _ hFull
  obtain ⟨d0, hd0, hle0⟩ := exists_le_bnd _ hL
  have hLd : Ld D u i hi c ≤ bnd d := hle
  have hLd_sp := dual_span (sigD D : D.host.E →+* D.host.E) (gramN D i hi) _ hL
  refine ⟨exists_isLocBasis _ _ _ (fg_of_le_bnd hd hLd) hLd_sp, fun v => exists_isLocBasis _ _ _ ?_ ?_⟩
  · refine fg_of_le_bnd (mul_ne_zero hd hd0) (sup_le (hle0.trans (bnd_mono d0 d)) ?_)
    refine (Submodule.smul_le_right.trans hLd).trans ?_
    rw [mul_comm]
    exact bnd_mono d d0
  · apply eq_top_iff.2
    rw [← hLd_sp]
    apply Submodule.span_le.2
    intro z hz
    have ht : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast (D.mem u).A.T_prime.ne_zero
    have hm : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ A.Pv v := by
      show A.res v _ = 0
      rw [map_natCast, ← (D.mem u).A.card_Fv v]
      exact FiniteField.cast_card_eq_zero _
    have hz' : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z ∈ Lk A i hi v c :=
      Submodule.mem_sup_right (Submodule.smul_mem_smul hm hz)
    have h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z ∈
        Submodule.span D.host.E (Lk A i hi v c : Set _) := Submodule.subset_span hz'
    have hfield : (((D.mem u).A.T : ℕ) : D.host.E) • z ∈
        Submodule.span D.host.E (Lk A i hi v c : Set _) := by
      change (algebraMap (𝓞 D.host.E) D.host.E (((D.mem u).A.T : ℕ) : 𝓞 D.host.E)) • z ∈ _
      rw [IsScalarTower.algebraMap_smul]
      exact h
    have h' := (Submodule.span D.host.E (Lk A i hi v c : Set (Fin (D.R.N i) → D.host.E))).smul_mem
      ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹) hfield
    simpa [smul_smul, ht] using h'

def OntoAll (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ T : Forms0 D u, admS D u → ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
    ∀ B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E,
      (∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c)) →
      (∀ c, IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) (B' c)) →
      OntoAt T w v B B'

theorem second_branch_coordinates_of_surjectivity {D : D7} {u : D.what₂.Word} (h : OntoAll D u) : SecondBranchCoordinates D u := by
  intro T hA w hw hs v hb
  choose B hB using fun c => (locBases T.atT 0 (Nat.zero_le _) c).1
  choose B' hB' using fun c => (locBases T.atT 0 (Nat.zero_le _) c).2 v
  refine ⟨B, B', hB, hB', fun c => ?_, h T hA w hw hs v hb B B' hB hB'⟩
  exact V0.det_basis_change_unit_zero D u T (Formalism.L2.Host.second_unramified_condition_holds (D := D) (u := u) T.atT) w hw hs v 0 (Nat.zero_le _) rfl c
    (B c) (B' c) (hB c) (hB' c)

theorem second_branch_of_surjectivity (hO : ∀ (D : D7) (u : D.what₂.Word), OntoAll D u)
    (hd : ∀ (D : D7) (u : D.what₂.Word), Forms0 D u → admS D u → DuCount D u) :
    ∀ (D : D7) (u : D.what₂.Word), Formalism.MainNotions.RT.SecondBranchIntegralityUnderForms D u :=
  second_branch_of_coordinates_and_count (fun D u => second_branch_coordinates_of_surjectivity (hO D u)) hd

end Formalism.L2.GlobalTheoryTheory.LemB
end
end

