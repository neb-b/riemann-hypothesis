module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.UniqInvHolds
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UniformizationHolds
section
noncomputable section

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

abbrev cj : ℂ →+ ℂ := (starRingEnd ℂ).toAddMonoidHom

theorem cj_apply (z : ℂ) : cj z = starRingEnd ℂ z := rfl

theorem map_cj_map_cj (Λ : AddSubgroup ℂ) : (Λ.map cj).map cj = Λ := by
  rw [AddSubgroup.map_map]
  have : cj.comp cj = AddMonoidHom.id ℂ := by ext z; simp [cj_apply]
  rw [this, AddSubgroup.map_id]

theorem eisG_map_cj (Λ : AddSubgroup ℂ) (k : ℕ) :
    eisG (Λ.map cj) k = starRingEnd ℂ (eisG Λ k) := by
  unfold eisG
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ Λ.map cj ∧ w ≠ 0} :=
    { toFun := fun w => ⟨starRingEnd ℂ w.1, ⟨w.1, w.2.1, rfl⟩, by simpa using w.2.2⟩
      invFun := fun w => ⟨starRingEnd ℂ w.1, by
          obtain ⟨v, hv, hv'⟩ := AddSubgroup.mem_map.1 w.2.1
          have : starRingEnd ℂ w.1 = v := by rw [← hv']; simp [cj_apply]
          rw [this]; exact hv, by simpa using w.2.2⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  rw [← e.tsum_eq, Complex.conj_tsum]
  congr 1
  ext w
  show (1 : ℂ) / (starRingEnd ℂ (w : ℂ)) ^ (2 * k) = starRingEnd ℂ (1 / (w : ℂ) ^ (2 * k))
  simp [map_div₀, map_pow]

theorem eisenstein_g_two_map_conj (Λ : AddSubgroup ℂ) : g2 (Λ.map cj) = starRingEnd ℂ (g2 Λ) := by
  unfold g2; rw [eisG_map_cj, map_mul, map_ofNat]

theorem eisenstein_g_three_map_conj (Λ : AddSubgroup ℂ) : g3 (Λ.map cj) = starRingEnd ℂ (g3 Λ) := by
  unfold g3; rw [eisG_map_cj, map_mul, map_ofNat]

theorem discr_map_cj (Λ : AddSubgroup ℂ) :
    Formalism.MainNotions.TaylorLogMetric.discr (Λ.map cj) = starRingEnd ℂ (Formalism.MainNotions.TaylorLogMetric.discr Λ) := by
  unfold Formalism.MainNotions.TaylorLogMetric.discr; rw [eisenstein_g_two_map_conj, eisenstein_g_three_map_conj, map_sub, map_mul, map_pow, map_pow, map_ofNat]

theorem lamConj_spec (hU : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization) (M : IntermediateField ℚ ℂ)
    (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) (h1 : Formalism.MainNotions.TaylorLogMetric.discr Λ = 1) :
    g2 (lamConj M ρ Λ) = ρ ⟨g2 Λ, h2⟩ ∧ g3 (lamConj M ρ Λ) = ρ ⟨g3 Λ, h3⟩ ∧
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ Λ) = 1 := by
  have hl2 : liftM M (g2 Λ) = ⟨g2 Λ, h2⟩ := dif_pos h2
  have hl3 : liftM M (g3 Λ) = ⟨g3 Λ, h3⟩ := dif_pos h3
  have hdM : (⟨g2 Λ, h2⟩ : M) ^ 3 - 27 * (⟨g3 Λ, h3⟩ : M) ^ 2 = 1 := by
    apply M.val.injective
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one]
    exact h1
  have hab : (ρ ⟨g2 Λ, h2⟩) ^ 3 - 27 * (ρ ⟨g3 Λ, h3⟩) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hdM, map_one]
  obtain ⟨Λ', -, h2', h3'⟩ := (hU _ _ (by rw [hab]; exact one_ne_zero)).1
  have hex : ∃ Λ' : AddSubgroup ℂ, g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)) :=
    ⟨Λ', by rw [hl2]; exact h2', by rw [hl3]; exact h3'⟩
  have hs := Classical.epsilon_spec hex
  have e2 : g2 (lamConj M ρ Λ) = ρ ⟨g2 Λ, h2⟩ := hs.1.trans (by rw [hl2])
  have e3 : g3 (lamConj M ρ Λ) = ρ ⟨g3 Λ, h3⟩ := hs.2.trans (by rw [hl3])
  refine ⟨e2, e3, ?_⟩
  show g2 _ ^ 3 - 27 * g3 _ ^ 2 = 1
  rw [e2, e3, hab]

def conjO (D : D7) : 𝓞 D.host.K ≃+* 𝓞 D.host.K :=
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  RingOfIntegers.mapRingEquiv
    ((AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K ≃ₐ[ℚ] D.host.K) : D.host.K ≃+* D.host.K)

theorem phi_conjO (D : D7) (a : 𝓞 D.host.K) :
    D.host.φ₀ (((conjO D a : 𝓞 D.host.K) : D.host.K) : D.host.E) =
      starRingEnd ℂ (D.host.φ₀ ((a : D.host.K) : D.host.E)) := by
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  have h : (((conjO D a : 𝓞 D.host.K) : D.host.K) : D.host.E) = D.host.conj ((a : D.host.K) : D.host.E) := by
    rw [conjO, RingOfIntegers.mapRingEquiv_apply]
    exact AlgEquiv.restrictNormal_commutes D.host.conj D.host.K (a : D.host.K)
  rw [h]
  exact D.host.toHostAx.conjE_apply _ _

theorem lamOf_map_cj (D : D7) (c : Ideal (𝓞 D.host.K)) (x : ℂ) :
    (lamOf D c x).map cj = lamOf D (c.map (conjO D)) (starRingEnd ℂ x) := by
  unfold lamOf
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨conjO D a, Ideal.mem_map_of_mem _ ha, ?_⟩
    rw [phi_conjO, cj_apply, map_mul]
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.mem_map_of_equiv] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨_, ⟨a, ha, rfl⟩, by rw [phi_conjO, cj_apply, map_mul]⟩

end GlobalTheory.ConjLattice

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem containsData {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {M : IntermediateField ℚ ℂ}
    (h : DataIn D (tor0 D cc δ) M) : EquidistributedConjugates.ContainsData D M (lamOf D cc δ) := by
  refine ⟨fun x => ?_, h.2.1, h.2.2⟩
  have := h.1 (D.eTau.symm 1) (x : D.host.E)
  rwa [show (tor0 D cc δ).emb (D.eTau.symm 1) (x : D.host.E) = embT D (D.eTau.symm 1) (x : D.host.E) from rfl,
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D _ _ x.2] at this

theorem conj_lattice : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization →
    EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta →
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  intro hU hCE _ D cc δ M _ t hS ρ
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have h1 : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have h2 : g2 (lamOf D cc δ) ∈ M := hM.2.1
  have h3 : g3 (lamOf D cc δ) ∈ M := hM.2.2
  have hsp := fun ρ' => lamConj_spec hU M ρ' (lamOf D cc δ) h2 h3 h1
  refine ⟨(hsp ρ).2.2, ?_⟩
  obtain ⟨⟨c, hcH, -⟩, hC2, -⟩ := hCE D cc δ hcc hδ M (containsData hM)
  by_cases hρ : EquidistributedConjugates.FixesK D M ρ
  · obtain ⟨x, hx, hxe⟩ := hcH ⟨ρ, hρ⟩
    exact ⟨_, nonZeroDivisors.coe_ne_zero _, x, hx, hxe⟩
  · obtain ⟨hρ', -⟩ := hC2 ρ hρ
    obtain ⟨x, hx, hxe⟩ := hcH ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩
    have hUI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.UniqInv :=
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqInv_of_lat Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds hU
    have hmap : (lamConj M ρ (lamOf D cc δ)).map cj = lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ) := by
      apply hUI
      · rw [discr_map_cj, (hsp ρ).2.2, map_one]; exact one_ne_zero
      · rw [eisenstein_g_two_map_conj, (hsp ρ).1, (hsp _).1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
      · rw [eisenstein_g_three_map_conj, (hsp ρ).2.1, (hsp _).2.1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
    have hback : lamConj M ρ (lamOf D cc δ) = (lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ)).map cj := by
      rw [← hmap, map_cj_map_cj]
    refine ⟨(c ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩ : Ideal (𝓞 D.host.K)).map (conjO D), ?_, starRingEnd ℂ x,
      (map_ne_zero _).2 hx, by rw [hback, hxe, lamOf_map_cj]⟩
    intro hbot
    rw [Ideal.map_eq_bot_iff_of_injective (conjO D).injective] at hbot
    exact nonZeroDivisors.coe_ne_zero _ hbot

end GlobalTheory.ConjLattice

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem uniformization_holds : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization := by
  intro a b h
  refine ⟨?_, fun Λ Λ' hΛ hΛ' h2 h3 h2' h3' =>
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqLat_holds Λ Λ' hΛ hΛ' (h2.trans h2'.symm) (h3.trans h3'.symm)⟩
  obtain ⟨L, h2, h3⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants h
  obtain ⟨e2, e3, hΔ, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)
  exact ⟨_, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds _ hΔ, e2.trans h2, e3.trans h3⟩

theorem conj_lattice_holds : EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta →
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x :=
  conj_lattice uniformization_holds

end GlobalTheory.ConjLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WtBoundsOfNonneg
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

variable {D : D7} {u : D.what₂.Word}

theorem natAbs_lamT_le_Wt (X : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j))
    (ha : ¬ (a.1 = 0 ∧ τ ∈ tops D)) : ((PtModel.lamT X j τ).w a).natAbs ≤ Wt X τ := by
  unfold Wt TauWeight
  refine le_trans ?_ (Finset.le_sup (f := fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  refine le_trans ?_ (Finset.le_sup (f := fun a : Fin (D.R.N j) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam j τ).w a - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs) (Finset.mem_univ a))
  rw [if_neg ha]
  exact le_rfl

theorem lamT_last (X : Ch D u) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N (i + 1)))
    (ha : a.1 = D.R.N (i + 1) - 1) : (PtModel.lamT X (i + 1) τ).w a = -X.C.sDiv i τ := by
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  have hm : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + D.R.t + 1 := by ring
  have ha' : a.1 = D.R.k + (D.R.t + i * (D.R.t + 1)) := by omega
  have hk : ¬ a.1 < D.R.k := by omega
  have hq : (a.1 - D.R.k) / (D.R.t + 1) = i := by
    rw [ha', Nat.add_sub_cancel_left, Nat.add_mul_div_right _ _ (Nat.succ_pos _),
      Nat.div_eq_of_lt (Nat.lt_succ_self _), zero_add]
  have h1 := X.fm.lam_eq (i + 1) hi τ a
  rw [dite_eq_right hk] at h1
  simp only [hq] at h1
  have h2 := X.C.sDiv_eq i hi τ
  obtain ⟨c, hc⟩ := D.R.t_odd
  have h3 : (i + 1) * (D.R.t + 1) / 2 = (i + 1) * (c + 1) := by
    have : (i + 1) * (D.R.t + 1) = 2 * ((i + 1) * (c + 1)) := by rw [hc]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hcq : (D.R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
  change (X.fm.lam (i + 1) τ).w a - (((i + 1) * (D.R.t + 1) / 2 : ℕ) : ℤ) = _
  rw [h3]
  have : (((X.fm.lam (i + 1) τ).w a - (((i + 1) * (c + 1) : ℕ) : ℤ) : ℤ) : ℚ) = ((-X.C.sDiv i τ : ℤ) : ℚ) := by
    push_cast
    rw [h1, h2]
    simp only [wG, sExp, Ranks.N, Nat.add_sub_cancel]
    push_cast
    rw [hcq]
    ring
  exact_mod_cast this

theorem wtBounds_of_nonneg : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u), (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) →
    (∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ) → WtBounds X := by
  intro D u X hb hs
  refine ⟨hb, fun i hi τ => ?_⟩
  have hpos := D.R.N_pos (i + 1)
  have hlast := lamT_last X i hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ rfl
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  refine ⟨hs i hi τ, ?_, ?_, fun hτ => ?_⟩
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ (fun h => by
      have := h.1
      simp only at this
      omega)
    rw [hlast] at h
    omega
  · unfold DomWeight.detShift
    rw [dite_eq_left hpos]
    exact hlast
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨0, hpos⟩ (fun h => hτ h.2)
    omega

end GlobalTheory.LvT
end

