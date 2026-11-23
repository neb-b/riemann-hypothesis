module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0270
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionsAllLevelsClosure
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaLevels

theorem bc_nsmul_left (D : D7) (T : Tor D) {N N' : ℕ} (n : ℕ) (x y : VC D N N') :
    bc D T (n • x) y = bc D T x y ^ n := by
  induction n with
  | zero => rw [zero_nsmul, bc_zero_left, pow_zero]
  | succ n ih => rw [succ_nsmul, bc_add_left, ih, pow_succ]

theorem bc_nsmul_right (D : D7) (T : Tor D) {N N' : ℕ} (n : ℕ) (x y : VC D N N') :
    bc D T x (n • y) = bc D T x y ^ n := by
  induction n with
  | zero => rw [zero_nsmul, bc_zero_right, pow_zero]
  | succ n ih => rw [succ_nsmul, bc_add_right, ih, pow_succ]

theorem wd_entire (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (Wd D T x G) := by
  unfold Wd U Hf
  fun_prop

theorem levels_closed : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (L : Lat D N) (L' : Lat D N'), SD D L → SD D L' → ∀ F ∈ Th D (tor0 D cc δ) L L', F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ (z : Matrix (Fin N') (Fin N) D.host.E), ∀ F ∈ TT D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ F ∈ TT D (tor0 D cc δ) N N', ∀ G ∈ TT D (tor0 D cc δ) N N', F + G ∈ TT D (tor0 D cc δ) N N') ∧ ∀ (a : ℂ), ∀ F ∈ TT D (tor0 D cc δ) N N', a • F ∈ TT D (tor0 D cc δ) N N' := by
  intro D cc δ hc N N'
  have hSD : ∀ n, SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
    rw [← h2]; exact (h1 _).2
  have k : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, hSD N, hSD N', rfl⟩
  have n0 := GlobalTheory.ThetaTriple.nice_of_klat hc k
  refine ⟨fun L L' hL hL' F hF => ?_, fun z F hF => ?_, fun F hF G hG => ?_, fun a F hF => ?_⟩
  · have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
    have n1 := GlobalTheory.ThetaTriple.nice_of_klat hc k1
    obtain ⟨hd, hF⟩ := (n1.mem_ThSp F).1 hF
    refine ⟨hd, _, Nat.pos_of_ne_zero (GlobalTheory.ThetaTriple.index_ne_zero hc k1 k), fun x hx => hF _ ?_⟩
    exact AddSubgroup.nsmul_index_mem
      ((La D (tor0 D cc δ) L L').addSubgroupOf (La0 D (tor0 D cc δ) N N')) ⟨x, hx⟩
  · obtain ⟨hd, m, hm, hF⟩ := hF
    obtain ⟨n, hn, hz⟩ := GlobalTheory.ThetaInter.klat_mul_mem (GlobalTheory.InducedType.induced_type D).1.1 hc.1.1 k z
    change n • pt D (tor0 D cc δ) δ z ∈ _ at hz
    refine ⟨wd_entire D _ _ hd, m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
    have hmx := AddSubgroup.nsmul_mem _ hx m
    have h1 : bc D (tor0 D cc δ) ((m * n) • x) (pt D (tor0 D cc δ) δ z) = 1 := by
      rw [mul_comm, mul_smul, bc_nsmul_left, ← bc_nsmul_right]
      exact n0.2.1 _ hmx _ hz
    have h2 : bc D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) ((m * n) • x) = 1 := by
      rw [mul_comm, mul_smul, bc_nsmul_right, ← bc_nsmul_left]
      exact n0.2.1 _ hz _ hmx
    have h3 : Wd D (tor0 D cc δ) ((m * n) • x) F = F := by
      rw [mul_smul]; exact hF _ (AddSubgroup.nsmul_mem _ hx n)
    have h4 := Wd_Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) ((m * n) • x) F
    rw [h3, h2, add_comm] at h4
    rw [Wd_Wd, h1, h4]
  · obtain ⟨hd, m, hm, hF⟩ := hF
    obtain ⟨hd', n, hn, hG⟩ := hG
    refine ⟨hd.add hd', m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
    have h1 : Wd D (tor0 D cc δ) ((m * n) • x) F = F := by
      rw [mul_smul]; exact hF _ (AddSubgroup.nsmul_mem _ hx n)
    have h2 : Wd D (tor0 D cc δ) ((m * n) • x) G = G := by
      rw [mul_comm, mul_smul]; exact hG _ (AddSubgroup.nsmul_mem _ hx m)
    rw [Wd_add, h1, h2]
  · obtain ⟨hd, m, hm, hF⟩ := hF
    exact ⟨hd.const_smul a, m, hm, fun x hx => by rw [Wd_smul, hF x hx]⟩

end GlobalTheory.ThetaLevels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaIntertwinerEqNormalisedAdelicSum
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.IopSum

theorem act_inv_act {D : D7} {N N' : ℕ} (u : GA D N × GA D N') (ζ : XA D N N') :
    actA D N N' u⁻¹ (actA D N N' u ζ) = ζ := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem act_act_inv {D : D7} {N N' : ℕ} (u : GA D N × GA D N') (ζ : XA D N N') :
    actA D N N' u (actA D N N' u⁻¹ ζ) = ζ := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem mem_map_act {D : D7} {N N' : ℕ} (A : Submodule (𝓞 D.host.E) (XA D N N')) (u : GA D N × GA D N') (ζ : XA D N N') :
    ζ ∈ A.map (actA D N N' u) ↔ actA D N N' u⁻¹ ζ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [act_inv_act]
  · intro h
    exact ⟨_, h, act_act_inv u ζ⟩

theorem mem_moved {D : D7} {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} (g : GA D N) (g' : GA D N') (ζ : XA D N N') :
    ζ ∈ (latA D cc N N').map (actA D N N' (g, g')) ↔
      ∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * ζ *
        ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc := by
  rw [mem_map_act, Prod.inv_mk, actA_apply, mem_latA, Subgroup.coe_inv, Subgroup.coe_inv, inv_inv]

theorem pt_sub {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z z' : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z - z') = pt D (tor0 D cc δ) δ z - pt D (tor0 D cc δ) δ z' := by
  funext τ i j
  simp [pt, embV, tor0, mul_sub]

theorem sd_of_moves {D : D7} {N : ℕ} (g : GA D N) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  have : L = Lt g := Submodule.ext fun x => (h x).trans ((hLt g).1 x).symm
  rw [this]
  exact (hLt g).2

end GlobalTheory.FinWeil.IopSum

namespace GlobalTheory.FinWeil

open IopSum

theorem iop_eq_sumOp : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → SelfDual γ ((latA D cc N N').map (actA D N N' (g, g'))) → ∀ F : TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') F → Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') F = ((Real.sqrt (idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) : ℝ))⁻¹ : ℂ) • ((sumOp WA (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) F : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) := by
  intro D hG cc δ hC N N' w γ WA hM g g' L₁ L₁' hL hL' hSD F hF
  obtain ⟨hlat1, -, hlat3, -⟩ := _root_.GlobalTheory.CompletedLattice.completed_lattice D hG cc δ hC N N'
  have hidx := (_root_.GlobalTheory.FinWeil.idx_map_actA D hG cc δ hC N N' g g').1
  have hidx' := (_root_.GlobalTheory.FinWeil.idx_map_actA D hG cc δ hC N N' g⁻¹ g'⁻¹).1
  have hA := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hC.1.1 N N' g g' L₁ L₁' hL hL'
  have hB := GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hC.1.1 N N' g g' L₁ L₁' hL hL'
  have hW := (GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (La D (tor0 D cc δ) L₁ L₁')
    (Or.inr ⟨L₁, L₁', sd_of_moves g hL, sd_of_moves g' hL', rfl⟩)).2.1
  simp only [← mem_moved] at hA hB
  set A := latA D cc N N' with hAdef
  set B := A.map (actA D N N' (g, g')) with hBdef
  set La₂ := La D (tor0 D cc δ) L₁ L₁' with hLa₂
  set La₁ := La0 D (tor0 D cc δ) N N' with hLa₁

  have hm : ∀ a ∈ A, idx A (A.map (actA D N N' (g⁻¹, g'⁻¹))) • a ∈ B := by
    intro a ha
    rw [hBdef, mem_map_act, map_nsmul, Prod.inv_mk]
    exact AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup
      (K := (A.map (actA D N N' (g⁻¹, g'⁻¹))).toAddSubgroup) ⟨a, ha, rfl⟩
  choose z hz hzB using fun q : La₂ ⧸ La₁.addSubgroupOf La₂ => hA _ (Quotient.out q).2
  have hsub : ∀ x y : Matrix (Fin N') (Fin N) D.host.E, x.map (inc D) - y.map (inc D) ∈ A ↔
      pt D (tor0 D cc δ) δ x - pt D (tor0 D cc δ) δ y ∈ La₁ := by
    intro x y
    rw [← Matrix.map_sub _ (map_sub (inc D)), hlat1, pt_sub]
  have huniq : ∀ q q', (z q).map (inc D) - (z q').map (inc D) ∈ A → q = q' := by
    intro q q' h
    rw [hsub, ← hz, ← hz] at h
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', eq_comm, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using h
  have htr : ∀ b ∈ B, ∃! q, b - (z q).map (inc D) ∈ A := by
    intro b hb
    obtain ⟨y, a, ha, hy⟩ := hlat3 b _ (Nat.pos_of_ne_zero hidx')
    have hyB : y.map (inc D) ∈ B := hy ▸ B.add_mem hb (hm a ha)
    have hex : b - (z (QuotientAddGroup.mk ⟨_, hB y hyB⟩)).map (inc D) ∈ A := by
      have h1 : y.map (inc D) - (z (QuotientAddGroup.mk ⟨_, hB y hyB⟩)).map (inc D) ∈ A := by
        rw [hsub, ← hz]
        have h2 := QuotientAddGroup.out_eq' (QuotientAddGroup.mk ⟨_, hB y hyB⟩ : La₂ ⧸ La₁.addSubgroupOf La₂)
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h2
        simpa [neg_add_eq_sub] using h2
      have h3 := A.sub_mem h1 (nsmul_mem ha (idx A (A.map (actA D N N' (g⁻¹, g'⁻¹)))))
      rw [hy] at h3
      convert h3 using 1
      abel
    refine ⟨QuotientAddGroup.mk ⟨_, hB y hyB⟩, ?_, ?_⟩
    · exact hex
    · intro q hq
      refine huniq _ _ ?_
      have := A.sub_mem hex hq
      rwa [sub_sub_sub_cancel_left] at this
  haveI : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hidx
  haveI : Finite (La₂ ⧸ La₁.addSubgroupOf La₂) := by
    refine Finite.of_injective (fun q => (QuotientAddGroup.mk ⟨_, hzB q⟩ :
      B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)) fun q q' h => ?_
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    refine (huniq q' q ?_).symm
    simpa [neg_add_eq_sub] using h
  haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)
  obtain ⟨h1, h2⟩ := (GlobalTheory.FinWeil.sumOp_transversal hM.1 A B hSD).1 F hF _ (fun q => (z q).map (inc D)) hzB htr
  rw [h1, h2]
  funext v
  rw [Iop, finsum_eq_sum_of_fintype, AddSubgroup.index, Nat.card_eq_fintype_card, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sum, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hM.2.2.2.1, ← hz, hW _ (Quotient.out q).2]

end GlobalTheory.FinWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPairCoordinatesConjugateBound
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.CoordConj

theorem cj_coe (ρ : Qbar →ₐ[ℚ] ℂ) (w : Qbar) : cj Qbar ρ (w : ℂ) = ρ w := by
  simp [cj, TaylorLogMetric.liftM]

theorem differentiable_U {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (U D T x G) := by
  have h : Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
    unfold Hf
    fun_prop
  unfold U
  fun_prop

theorem differentiable_Iop {D : D7} {T : Tor D} {N N' : ℕ} (A B : AddSubgroup (VC D N N')) {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (Iop D T A B G) := by
  unfold Iop
  by_cases h : (A.addSubgroupOf B).index = 0
  · simp [h]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
    haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    simp only [finsum_eq_sum_of_fintype]
    exact (Differentiable.fun_sum fun q _ => (differentiable_U _ hG).const_mul _).const_mul _

theorem applyAt0_comb {D : D7} {a d : ℕ} {ι : Type} (s : Finset ι) (c : ι → ℂ) (G : ι → VC D a d → ℂ)
    (hG : ∀ i, Differentiable ℂ (G i)) (p : MvPolynomial (GL3Theta.Idx D a d) ℂ) :
    GL3Theta.applyAt0 D p (∑ i ∈ s, c i • G i) = ∑ i ∈ s, c i * GL3Theta.applyAt0 D p (G i) := by
  induction s using Finset.induction_on with
  | empty =>
    have h := (_root_.GlobalTheory.NormSum.applyAt0_minorPol_linear D a d (fun _ => 0) 0 (differentiable_const 0)).2.2.1 0 p
    simpa using h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      (_root_.GlobalTheory.NormSum.applyAt0_minorPol_linear D a d (fun _ => 0) _ ((hG i).const_smul (c i))).2.2.2 _ p
        (Differentiable.sum fun j _ => (hG j).const_smul (c j)), ih,
      (_root_.GlobalTheory.NormSum.applyAt0_minorPol_linear D a d (fun _ => 0) _ (hG i)).2.2.1]

theorem comb_bound {ι : Type} [Fintype ι] (ρ : Qbar →ₐ[ℚ] ℂ) (r : ι → Qbar) (t : ι → ℂ) (S M : ℝ) (hM : 0 ≤ M)
    (hr : (∑ i, ‖ρ (r i)‖) ^ 2 ≤ S) (ht : ∀ i, t i ∈ Qbar ∧ ‖cj Qbar ρ (t i)‖ ^ 2 ≤ M) :
    ∑ i, (r i : ℂ) * t i ∈ Qbar ∧ ‖cj Qbar ρ (∑ i, (r i : ℂ) * t i)‖ ^ 2 ≤ S * M := by
  have e : ∑ i, (r i : ℂ) * t i = ((∑ i, r i * ⟨t i, (ht i).1⟩ : Qbar) : ℂ) := by
    push_cast
    rfl
  refine ⟨e ▸ SetLike.coe_mem _, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, cj_coe, map_sum]
  have h1 : ∀ i, ‖ρ ⟨t i, (ht i).1⟩‖ ≤ Real.sqrt M := fun i => by
    rw [← cj_coe]
    exact Real.le_sqrt_of_sq_le (ht i).2
  have h2 : ‖∑ i, ρ (r i * ⟨t i, (ht i).1⟩)‖ ≤ (∑ i, ‖ρ (r i)‖) * Real.sqrt M := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (h1 i) (norm_nonneg _)
  calc _ ≤ ((∑ i, ‖ρ (r i)‖) * Real.sqrt M) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = (∑ i, ‖ρ (r i)‖) ^ 2 * M := by rw [mul_pow, Real.sq_sqrt hM]
    _ ≤ S * M := mul_le_mul_of_nonneg_right hr hM

theorem coord_conj_le : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  intro D hI cc δ t0 Q hc ht0 P hQ B hB hn ρ t0' ht0' h T
  generalize hM : (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) = M
  have hev : Even (P.a * P.d) := P.d_even.mul_left _
  obtain ⟨Lt, hL, hL1, -⟩ := _root_.GlobalTheory.NormSum.exists_lattice_of_adelic_point D P.a
  obtain ⟨Lt', hL', hL1', -⟩ := _root_.GlobalTheory.NormSum.exists_lattice_of_adelic_point D P.d
  have hs : SD D (stdL D P.a) := hL1 ▸ (hL 1).2
  have hs' : SD D (stdL D P.d) := hL1' ▸ (hL' 1).2
  have hjet : ∀ L L', SD D L → SD D L' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G →
      ∀ y, LaQ D (tor0 D cc δ) L L' y →
      GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧
        ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ M := by
    intro L L' h1 h2 G hG y hy
    rw [← hM]
    exact _root_.GlobalTheory.ConjJet.conj_jet_bound D hI cc δ t0 hc ht0 P.a P.d L L' h1 h2 hev G hG y hy P.n B hB hn ρ t0' ht0' T
  have hM0 : 0 ≤ M :=
    (sq_nonneg _).trans (hjet _ _ hs hs' P.e0 P.vac.2.2.2.1 0 ⟨1, one_pos, by simp⟩).2
  have hterm : ∀ x, P.term x h T ∈ Qbar ∧ ‖cj Qbar ρ (P.term x h T)‖ ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d) * M := by
    intro x
    obtain ⟨c, k, r, y, hy⟩ := _root_.GlobalTheory.NormSum.Expand.om_expand D hI cc δ t0 Q hc ht0 P x h (Lt x) (Lt' h) (hL x).1 (hL' h).1
    obtain ⟨⟨hcQ, hc1⟩, hy, -, hr, hF, -⟩ := hy hQ
    have hG := _root_.GlobalTheory.VacuumMove.isVacuum_thetaIntertwiner_selfDual D hI cc δ t0 hc ht0 P.a P.d _ _ (Lt x) (Lt' h) hs hs' (hL x).2 (hL' h).2 P.e0
      P.vac.2.2.2.1
    have hGd := differentiable_Iop (T := tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.vac.1.1
    change ThetaVectorUpToUnits D (tor0 D cc δ) t0 (Lt x) (Lt' h) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.e0) at hG
    generalize Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.e0 = G at hG hGd hF
    have e : P.W.Om x h P.F = ∑ i, (((⟨c, hcQ⟩ * r i : Qbar) : ℂ)) • U D (tor0 D cc δ) (y i) G := by
      rw [hF]
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, MulMemClass.coe_mul, mul_assoc]
    unfold Pair.term
    rw [e, applyAt0_comb _ _ _ fun i => differentiable_U _ hGd]
    refine comb_bound ρ _ _ _ _ hM0 ?_ fun i => hjet _ _ (hL x).2 (hL' h).2 G hG _ ⟨Q, hQ, hy i⟩
    have h1 : ‖ρ ⟨c, hcQ⟩‖ = 1 := hc1 (ρ : Qbar →+* ℂ)
    simp only [map_mul, norm_mul, h1, one_mul]
    exact hr (ρ : Qbar →+* ℂ)
  haveI := (_root_.GlobalTheory.NormSum.cls_finite_card_le D P.a).1
  haveI := Fintype.ofFinite (Cls D P.a (intG D P.a))
  have e : P.coord h T = ∑ x : Cls D P.a (intG D P.a),
      ((((gam D (intG D P.a) x.out : Qbar))⁻¹ : Qbar) : ℂ) * P.term x.out h T := by
    unfold Pair.coord
    rw [finsum_eq_sum_of_fintype]
    simp
  rw [e, mul_assoc]
  refine comb_bound ρ _ _ _ _ (by positivity) ?_ fun x => hterm _
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [Nat.card_eq_fintype_card, Fintype.card, Finset.card_eq_sum_ones]
  push_cast
  refine Finset.sum_le_sum fun x _ => ?_
  rw [map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]
  exact Nat.cast_inv_le_one _

end GlobalTheory.NormSum.CoordConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionTranslatesSpanTaylorCoeffsAlgebraic
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj

private theorem cj_val {M : IntermediateField ℚ ℂ} {x : ℂ} (h : x ∈ M) : cj M M.val x = x := by
  exact cj_mem M.val h

private theorem emb_mem_Qbar (D : D7) (e : D.host.E →+* ℂ) (x : D.host.E) : e x ∈ Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ (e.toRatAlgHom x) := hx.algHom _
  exact mem_algebraicClosure_iff.mpr this

private theorem differentiable_U1 (Λ : AddSubgroup ℂ) (ω : ℂ) {G : ℂ → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (U1 Λ ω G) := by
  unfold U1
  fun_prop

private theorem U_pullB_eq_prod (D : D7) (h : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b) (g : ℂ → ℂ) (t : VC D N N') :
    U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b g) = fun z =>
      ∏ j, U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) g (coordB D (tor0 D cc δ) b j z) := by
  have hP := (GlobalTheory.OnCoord.coords_of_orthonormal_basis D h cc δ N N' r b hb).2.2.1
  funext z
  unfold U U1 pullB Hf
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
  congr 1
  · simp only [coordB_add]
  · congr 1
    change _ = ∑ j, (_ / (area (tor0 D cc δ).abelian₂ : ℂ) - _ / (2 * (area (tor0 D cc δ).abelian₂ : ℂ)))
    rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem translates_coef_algebraic : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ F ∈ Tr D (tor0 D cc δ) b, Differentiable ℂ F ∧ CoefIn D F Qbar := by
  intro D cc δ hC N N' r b hb F hF
  have h : admG1 D := (GlobalTheory.InducedType.induced_type D).1
  have hlat := (GlobalTheory.CurveLattice.lattice_of_curve D h cc δ hC).1
  have hσ : Differentiable ℂ (sgStar (lamOf D cc δ)) := (GlobalTheory.OddTheta.sgStar_laws _ hlat).1.1
  have hL := (GlobalTheory.OnCoord.coords_of_orthonormal_basis D h cc δ N N' r b hb).2.2.2.1
  unfold Tr at hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨t, ⟨m, hm, hmt⟩, rfl⟩ := hF
    change Differentiable ℂ (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) ∧
      CoefIn D (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) Qbar
    rw [U_pullB_eq_prod D h cc δ hb]
    have hq : ∀ j, InRationalLattice (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) := fun j => by
      refine ⟨m, hm, ?_⟩
      rw [← coordB_smul, Nat.cast_smul_eq_nsmul]
      exact (hL _).1 hmt j
    have hl : ∀ j τ a c, (starRingEnd ℂ) ((tor0 D cc δ).emb τ (b j a c)) ∈ Qbar := fun j τ a c => by
      change (starRingEnd ℂ) (embT D τ (b j a c)) ∈ Qbar
      rw [← emb_conj]
      exact emb_mem_Qbar D _ _
    have key := _root_.GlobalTheory.ThetaConj.ProdLin.cjF_prod D N N' r Qbar Qbar.val
      (fun j => U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) (sgStar (lamOf D cc δ)))
      (fun j => U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) (sgStar (lamOf D cc δ)))
      (fun j τ a c => (starRingEnd ℂ) ((tor0 D cc δ).emb τ (b j a c)))
      (fun j τ a c => (starRingEnd ℂ) ((tor0 D cc δ).emb τ (b j a c)))
      (fun j => differentiable_U1 _ _ hσ) (fun j => differentiable_U1 _ _ hσ)
      (fun j n => by
        have := (_root_.GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hC).1 _ (hq j) n
        exact ⟨this, (cj_val this).symm⟩)
      (fun j τ a c => ⟨hl j τ a c, (cj_val (hl j τ a c)).symm⟩)
    exact ⟨key.1, fun α => (key.2.2 α).1⟩
  | zero => exact ⟨differentiable_const 0, fun α => by rw [taylor_zero]; exact zero_mem _⟩
  | add F G _ _ hF hG =>
    exact ⟨hF.1.add hG.1, fun α => by
      rw [taylor_add D hF.1 hG.1]; exact add_mem (hF.2 α) (hG.2 α)⟩
  | smul c F _ hF =>
    have : c • F = fun z => (c : ℂ) * F z := rfl
    rw [this]
    exact ⟨hF.1.const_mul _, fun α => by
      rw [taylor_mul D _ hF.1]; exact mul_mem c.2 (hF.2 α)⟩

end GlobalTheory.ThetaConj
end
end

