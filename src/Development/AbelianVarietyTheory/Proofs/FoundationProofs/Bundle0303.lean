module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairCoordinateConjugatesBounded
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.coord

theorem coord_conj_le : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  intro D cc δ t0 Q hc ht0 P hQ B hB hn ρ t0' ht0' h T
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
    exact _root_.GlobalTheory.ArchFree.jet.conj_jet_bound D cc δ t0 hc ht0 P.a P.d L L' h1 h2 hev G hG y hy P.n B hB hn ρ t0' ht0' T
  have hM0 : 0 ≤ M :=
    (sq_nonneg _).trans (hjet _ _ hs hs' P.e0 P.vac.2.2.2.1 0 ⟨1, one_pos, by simp⟩).2
  have hterm : ∀ x, P.term x h T ∈ Qbar ∧ ‖cj Qbar ρ (P.term x h T)‖ ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d) * M := by
    intro x
    obtain ⟨c, k, r, y, hy⟩ := _root_.GlobalTheory.ArchFree.expand.om_expand D cc δ t0 Q hc ht0 P x h (Lt x) (Lt' h) (hL x).1 (hL' h).1
    obtain ⟨⟨hcQ, hc1⟩, hy, -, hr, hF, -⟩ := hy hQ
    have hG := _root_.GlobalTheory.ArchFree.firstBasisVectorLike.isVacuum_thetaIntertwiner_selfDual D cc δ t0 hc ht0 P.a P.d _ _ (Lt x) (Lt' h) hs hs' (hL x).2 (hL' h).2 P.e0
      P.vac.2.2.2.1
    have hGd := GlobalTheory.NormSum.CoordConj.differentiable_Iop (T := tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
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
    rw [e, GlobalTheory.NormSum.CoordConj.applyAt0_comb _ _ _ fun i => GlobalTheory.NormSum.CoordConj.differentiable_U _ hGd]
    refine GlobalTheory.NormSum.CoordConj.comb_bound ρ _ _ _ _ hM0 ?_ fun i => hjet _ _ (hL x).2 (hL' h).2 G hG _ ⟨Q, hQ, hy i⟩
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
  refine GlobalTheory.NormSum.CoordConj.comb_bound ρ _ _ _ _ (by positivity) ?_ fun x => hterm _
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [Nat.card_eq_fintype_card, Fintype.card, Finset.card_eq_sum_ones]
  push_cast
  refine Finset.sum_le_sum fun x _ => ?_
  rw [map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]
  exact Nat.cast_inv_le_one _

end GlobalTheory.ArchFree.coord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
section
noncomputable section

namespace GlobalTheory.LFun.SplitChart

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

theorem continuous_complMap (h : w.under (𝓞 F) = v) : Continuous (complMap h) := by
  subst h
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have h0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp k :=
    ⟨_, (WithZero.exp_log h0).symm⟩
  filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := F) (w.under (𝓞 F)) (-((k.natAbs + 1 : ℕ) : ℤ))).mem_nhds
    (by simp)] with a ha
  rw [Valuation.restrict_lt_iff_lt_embedding, hk]
  exact (GlobalTheory.AdeleBaseChange.locMap_valued w _ a ha).trans_lt (WithZero.exp_lt_exp.2 (by omega))

theorem exists_splitPrime_eq (hc : IsCMExt F E σ) (hv : IsSplit (E := E) v) (h : w.under (𝓞 F) = v) :
    ∃ τ : E →ₐ[F] Fv F v, splitPrime τ = w := by
  obtain ⟨P, Q, hne, hP, hQ⟩ := hv
  by_cases e : w = P
  · exact (existsUnique_splitPrime_eq hc (e ▸ hne) h (HeightOneSpectrum.ext hQ)).exists
  · exact (existsUnique_splitPrime_eq hc e h (HeightOneSpectrum.ext hP)).exists

theorem exists_equiv_complMap (τ : E →ₐ[F] Fv F v) (h : (splitPrime τ).under (𝓞 F) = v) :
    ∃ ψ : Fv F v ≃+* (splitPrime τ).adicCompletion E, (∀ a, ψ a = complMap h a) ∧
      (∀ x : E, ψ (τ x) = algebraMap E _ x) ∧ (∀ a, Valued.v (ψ a) = Valued.v a) ∧ Continuous ψ ∧
      Continuous ψ.symm := by
  obtain ⟨φ, h1, h2, h3, h4⟩ := GlobalTheory.SplitCompletion.exists_ringEquiv_splitPrime τ
  have h5 : ∀ x : E, φ.symm (τ x) = algebraMap E _ x := fun x => by rw [← h1, φ.symm_apply_apply]
  refine ⟨φ.symm, congrFun ((HeightOneSpectrum.denseRange_algebraMap F v).equalizer h4 (continuous_complMap h)
    (funext fun a => ?_)), h5, fun a => by rw [← h2, φ.apply_symm_apply], h4, h3⟩
  exact ((congrArg φ.symm (τ.commutes a).symm).trans (h5 _)).trans (complMap_algebraMap h a).symm

section Transport

variable {τ : E →ₐ[F] Fv F v} {h : w.under (𝓞 F) = v} {ψ : Fv F v ≃+* w.adicCompletion E}

theorem toCompl_eq (h1 : ∀ a, ψ a = complMap h a) (h2 : ∀ x : E, ψ (τ x) = algebraMap E _ x)
    (y : Fv F v ⊗[F] E) : toCompl h y = ψ (splitProj τ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rw [toCompl_tmul, splitProj_tmul, map_mul, h1, h2]

omit [Algebra F E] in
theorem map_mem_Ov_iff (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) {a : Fv F v} :
    ψ a ∈ Ov E w ↔ a ∈ v.adicCompletionIntegers F := by
  change Valued.v (ψ a) ≤ 1 ↔ Valued.v a ≤ 1
  rw [h3]

theorem map_mem_latAt_iff (h2 : ∀ x : E, ψ (τ x) = algebraMap E _ x) (h3 : ∀ a, Valued.v (ψ a) = Valued.v a)
    {u : Fin n → Fv F v} : (fun i => ψ (u i)) ∈ latAt w L ↔ u ∈ splitLat τ L := by
  constructor
  · intro hu
    have key : ∀ y ∈ latAt w L, (fun i => ψ.symm (y i)) ∈ splitLat τ L := fun y hy => by
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        refine ⟨_, tmul_mem_latLoc (one_mem _) hz, funext fun i => ?_⟩
        change splitProj τ (1 ⊗ₜ[F] z i) = ψ.symm (algebraMap E _ (z i))
        rw [splitProj_tmul, one_mul, ← h2, ψ.symm_apply_apply]
      | zero => exact (funext fun _ => map_zero ψ.symm : (fun i => ψ.symm ((0 : Fin n → _) i)) = 0) ▸ zero_mem _
      | add a b _ _ ha hb =>
        have := add_mem ha hb
        convert this using 1
        exact funext fun i => map_add ψ.symm _ _
      | smul a b _ hb =>
        have := (splitLat τ L).smul_mem ⟨ψ.symm a, (map_mem_Ov_iff h3).1 (by rw [ψ.apply_symm_apply]; exact a.2)⟩ hb
        convert this using 1
        exact funext fun i => map_mul ψ.symm _ _
    simpa using key _ hu
  · rintro ⟨y, hy, rfl⟩
    refine latLoc_induction (p := fun y => (fun i => ψ (splitVec τ y i)) ∈ latAt w L) (fun a ha x hx => ?_) ?_
      (fun y z hy hz => ?_) (fun y hy => ?_) hy
    · have := (latAt w L).smul_mem ⟨ψ a, (map_mem_Ov_iff h3).2 ha⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)
      convert this using 1
      funext i
      change ψ (a * τ (x i)) = ψ a * algebraMap E _ (x i)
      rw [map_mul, h2]
    · convert zero_mem (latAt w L) using 1
      funext i
      simp [splitVec]
    · convert add_mem hy hz using 1
      funext i
      simp [splitVec]
    · convert neg_mem hy using 1
      funext i
      simp [splitVec]

theorem isFrameAt_bc (h2 : ∀ x : E, ψ (τ x) = algebraMap E _ x) (h3 : ∀ a, Valued.v (ψ a) = Valued.v a)
    {β : GL (Fin n) (Fv F v)} (hβ : IsSplitBasis τ L β) : IsFrameAt w L (bc ψ.toRingHom β) := fun y => by
  obtain ⟨u, rfl⟩ : ∃ u : Fin n → Fv F v, y = fun i => ψ (u i) := ⟨fun i => ψ.symm (y i), by simp⟩
  have e : (bc ψ.toRingHom β).1 *ᵥ (fun i => ψ (u i)) = fun i => ψ ((β.1 *ᵥ u) i) :=
    funext fun i => (RingHom.map_mulVec ψ.toRingHom β.1 u i).symm
  simp only [e, map_mem_Ov_iff h3, map_mem_latAt_iff h2 h3]
  exact hβ u

omit [Algebra F E] in
theorem bc_mem_KGL_iff (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) {x : GL (Fin n) (Fv F v)} :
    bc ψ.toRingHom x ∈ KGL w (n := n) ↔ x ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring := by
  rw [mem_GLint_iff, mem_GLint_iff]
  exact and_congr (forall₂_congr fun _ _ => map_mem_Ov_iff h3) (forall₂_congr fun _ _ => map_mem_Ov_iff h3)

end Transport

theorem continuous_bc {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    {f : A →+* B} (hf : Continuous f) : Continuous (bc (n := Fin n) f) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map hf, Units.continuous_coe_inv.matrix_map hf⟩

theorem exists_isSplitChart (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : L.FG)
    (hL' : Submodule.span E (L : Set (Fin n → E)) = ⊤) (h : w.under (𝓞 F) = v) (hv : IsSplit (E := E) v)
    (hd : IsSelfDualAt σ J L v) : ∃ e, IsSplitChart σ J L h e ∧ Continuous e ∧ Continuous e.symm := by
  obtain ⟨τ, rfl⟩ := exists_splitPrime_eq hc hv h
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := exists_equiv_complMap τ h
  letI : Submodule.IsFullLattice E L :=
    { toIsLattice := Submodule.IsLattice.of_fg E hL, span_eq_top := hL' }
  obtain ⟨β, hβ⟩ := exists_isSplitBasis τ L hc
  refine ⟨(splitEquivIn hc hJ τ β).toMulEquiv.trans (Units.mapEquiv ψ.mapMatrix.toMulEquiv),
    ⟨⟨_, isFrameAt_bc h2 h3 hβ, fun g => ?_⟩, fun g => ?_⟩,
    (continuous_bc (f := ψ.toRingHom) h4).comp (splitEquivIn hc hJ τ β).continuous,
    (splitEquivIn hc hJ τ β).symm.continuous.comp (continuous_bc (f := ψ.symm.toRingHom) h5)⟩
  · change bc ψ.toRingHom (β⁻¹ * splitHom σ J τ g * β) = _
    rw [map_mul, map_mul, map_inv]
    congr 2
    exact Units.ext (Matrix.ext fun i j => (toCompl_eq h1 h2 _).symm)
  · exact (mem_stabLoc_iff_GLint hc hJ hd hβ).trans (bc_mem_KGL_iff h3).symm

theorem absNorm_splitPrime (τ : E →ₐ[F] Fv F v) :
    Ideal.absNorm (splitPrime τ).asIdeal = Ideal.absNorm v.asIdeal := by
  have hle : v.asIdeal = (splitPrime τ).asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) :=
    (Ideal.ext (algebraMap_mem_splitPrime τ)).symm
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_eq_of_bijective (Ideal.quotientMap _ _ hle.le) ⟨Ideal.quotientMap_injective' hle.ge, fun y => ?_⟩).symm
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := ReciprocityTheory.Aut.adic_exists_approx v (τ x) (apply_coe_mem τ x)
  refine ⟨Ideal.Quotient.mk _ a, (Ideal.Quotient.eq.2 ((mem_splitPrime τ _).2 ?_)).symm⟩
  exact ((map_sub τ (x : E) (algebraMap F E a)).trans (congrArg _ (τ.commutes (a : F)))) ▸ ha

theorem exists_conj_place (hc : IsCMExt F E σ) (h : w.under (𝓞 F) = v) (hv : IsSplit (E := E) v) :
    ∃ w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ (∀ u, u.under (𝓞 F) = v ↔ u = w ∨ u = w') ∧
      Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal ∧
      w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (σ : E →+* E)) := by
  obtain ⟨τ, rfl⟩ := exists_splitPrime_eq hc hv h
  refine ⟨splitPrime (τ.comp σ), (splitPrime_comp_ne hc τ).symm, fun u => ⟨fun hu => ?_, ?_⟩, absNorm_splitPrime τ,
    absNorm_splitPrime _, Ideal.ext (mem_splitPrime_comp τ σ)⟩
  · obtain ⟨ρ, rfl⟩ := exists_splitPrime_eq hc hv hu
    exact (eq_or_eq_comp_conj hc τ ρ).imp (congrArg _) (congrArg _)
  · rintro (rfl | rfl) <;> exact splitPrime_under _

theorem split_chart_and_places (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : L.FG)
    (hL' : Submodule.span E (L : Set (Fin n → E)) = ⊤) (h : w.under (𝓞 F) = v) (hv : IsSplit (E := E) v)
    (hd : IsSelfDualAt σ J L v) :
    (∃ e, IsSplitChart σ J L h e ∧ Continuous e ∧ Continuous e.symm) ∧
      ∃ w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ (∀ u, u.under (𝓞 F) = v ↔ u = w ∨ u = w') ∧
        Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal ∧
        w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (σ : E →+* E)) :=
  ⟨exists_isSplitChart hc hJ hL hL' h hv hd, exists_conj_place hc h hv⟩

theorem isSplit_of_algHom (hc : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : IsSplit (E := E) v :=
  ⟨splitPrime (τ.comp σ), splitPrime τ, splitPrime_comp_ne hc τ, Ideal.ext (algebraMap_mem_splitPrime _),
    Ideal.ext (algebraMap_mem_splitPrime _)⟩

end GlobalTheory.LFun.SplitChart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EmbChart

open GlobalTheory.AdelicU

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))

def atPlace : Fv F v →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F)).comp (singleFin v)

theorem atPlace_apply (a : Fv F v) : atPlace v a = pairA F 0 (singleFin v a) := rfl

theorem atPlace_mul_right (a : Fv F v) (y : AF F) : atPlace v a * y = atPlace v (a * evFin F v y) := by
  refine Prod.ext (zero_mul _) ?_
  change singleFin v a * sndA F y = singleFin v (a * evalV F v (sndA F y))
  refine FiniteAdeleRing.ext _ fun u => ?_
  change evalV F u (singleFin v a * sndA F y) = evalV F u (singleFin v (a * evalV F v (sndA F y)))
  rw [map_mul]
  by_cases e : u = v
  · subst e; rw [evalV_singleFin_self, evalV_singleFin_self]
  · rw [evalV_singleFin_ne e, evalV_singleFin_ne e, zero_mul]

theorem evFin_atPlace (a : Fv F v) : evFin F v (atPlace v a) = a := evalV_singleFin_self v a


variable (E) in
def tensAt : Fv F v ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (atPlace v) LinearMap.id

theorem tensAt_tmul (a : Fv F v) (x : E) : tensAt E v (a ⊗ₜ[F] x) = atPlace v a ⊗ₜ[F] x := rfl

theorem compFin_tensAt (y : Fv F v ⊗[F] E) : compFin F E v (tensAt E v y) = y := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => exact congrArg (· ⊗ₜ[F] x) (evFin_atPlace v a)

theorem tensAt_eq_zero {y : Fv F v ⊗[F] E} : tensAt E v y = 0 ↔ y = 0 :=
  ⟨fun h => by rw [← compFin_tensAt v y, h, map_zero], fun h => by rw [h, map_zero]⟩

theorem tensAt_mul_right (y : Fv F v ⊗[F] E) (z : AF F ⊗[F] E) :
    tensAt E v y * z = tensAt E v (y * compFin F E v z) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), add_mul, hx, hy]
  | tmul a x =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add (f := _), mul_add, hx, hy]
    | tmul b x' =>
      change _ = tensAt E v (a ⊗ₜ[F] x * evFin F v b ⊗ₜ[F] x')
      rw [tensAt_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, tensAt_tmul,
        atPlace_mul_right]

theorem sigR_tensAt (σ : E →ₐ[F] E) (y : Fv F v ⊗[F] E) :
    sigR (AF F) σ (tensAt E v y) = tensAt E v (sigR _ σ y) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem map_evalV_map_sndA (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) =
      compFin F E v z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem map_evalV_mem {z : Af F ⊗[F] E}
    (hz : z ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) :
    Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) z ∈ intLoc F E v := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    exact tmul_mem_intLoc (hα v) o
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem map_sndA_tensAt_mem {y : Fv F v ⊗[F] E} (h : y ∈ intLoc F E v) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (tensAt E v y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  refine intLoc_induction (p := fun y => Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (tensAt E v y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)})
    (fun a ha x => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) h
  · refine AddSubgroup.subset_closure ⟨singleFin v a, fun u => ?_, x, rfl⟩
    by_cases e : u = v
    · subst e; rw [evalV_singleFin_self]; exact ha
    · rw [evalV_singleFin_ne e]; exact zero_mem _
  · rw [map_zero, map_zero]; exact zero_mem _
  · rw [map_add (f := _), map_add (f := _)]; exact add_mem hy hz
  · rw [map_neg, map_neg]; exact neg_mem hy

end General

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem finPart_tensAt_mem_iff (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    finPart D (tensAt D.host.E v y) ∈ intAE D ↔ y ∈ intLoc D.host.F D.host.E v := by
  refine ⟨fun h => ?_, map_sndA_tensAt_mem v⟩
  have h3 := map_evalV_mem v h
  rwa [show finPart D (tensAt D.host.E v y) = _ from rfl, finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_evalV_map_sndA, compFin_tensAt] at h3

def idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : AE D := tensAt D.host.E v (splitIdem (isCMExt_host D) τ)

theorem idem_mul (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (a : AE D) :
    idem τ * a = tensAt D.host.E v (splitIdem (isCMExt_host D) τ * compFin D.host.F D.host.E v a) :=
  tensAt_mul_right v _ a

theorem compFin_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    compFin D.host.F D.host.E v (idem τ) = splitIdem (isCMExt_host D) τ := compFin_tensAt v _

theorem cA_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    cA D (idem τ) = tensAt D.host.E v (1 - splitIdem (isCMExt_host D) τ) :=
  (sigR_tensAt v _ _).trans (congrArg _ (sigR_splitIdem _ τ))

theorem isSplitIdem_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : IsSplitIdem D (idem τ) := by
  refine ⟨?_, ?_, v, atPlace v 1, ⟨singleFin v 1, rfl, evalV_singleFin_self v 1, fun u hu => evalV_singleFin_ne hu 1⟩,
    ?_⟩
  · rw [idem_mul, compFin_idem, splitIdem_mul_self]; rfl
  · rw [idem_mul, cA_idem, compFin_tensAt, mul_sub, mul_one, splitIdem_mul_self, sub_self, LinearMap.map_zero]
  · rw [cA_idem, idem, ← LinearMap.map_add (f := _), add_sub_cancel]; rfl

theorem finPart_idem_mul_mem_iff (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (a : AE D) :
    finPart D (idem τ * a) ∈ intAE D ↔
      splitProj τ (compFin D.host.F D.host.E v a) ∈ v.adicCompletionIntegers D.host.F := by
  rw [idem_mul, finPart_tensAt_mem_iff, mem_intLoc_iff_split (isCMExt_host D) τ, map_mul, map_mul,
    splitProj_splitIdem, splitProj_comp_splitIdem, one_mul, zero_mul]
  exact and_iff_left (zero_mem _)

theorem chart_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Chart (idem τ) v
    ((splitProj τ : Fv D.host.F v ⊗[D.host.F] D.host.E →+* Fv D.host.F v).comp (compFin D.host.F D.host.E v)) := by
  refine ⟨fun a => ⟨tensAt D.host.E v (a ⊗ₜ 1), ?_⟩, fun a => ?_, fun y => ?_, fun a => ?_⟩
  · change splitProj τ (compFin D.host.F D.host.E v (tensAt D.host.E v (a ⊗ₜ[D.host.F] 1))) = a
    rw [compFin_tensAt, splitProj_tmul, map_one, mul_one]
  · rw [idem_mul, tensAt_eq_zero]
    exact splitProj_eq_zero_iff _ τ _
  · change splitProj τ (evFin D.host.F v y ⊗ₜ 1) = _
    rw [splitProj_tmul, map_one, mul_one]; rfl
  · rw [finPart_idem_mul_mem_iff, isInt_Ov]; rfl

theorem isIdemAt_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : IsIdemAt (idem τ) (splitPrime τ) := by
  refine ⟨isSplitIdem_idem τ, fun x hx => ?_⟩
  have h0 : Valued.v (τ x) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero τ).2 (RingOfIntegers.coe_ne_zero_iff.2 hx))
  have h1 : splitProj τ (compFin D.host.F D.host.E v (incA D (x : D.host.E)⁻¹)) = τ (x : D.host.E)⁻¹ := by
    change splitProj τ (evFin D.host.F v 1 ⊗ₜ _) = _
    rw [splitProj_tmul, map_one, one_mul]; rfl
  rw [finPart_idem_mul_mem_iff, h1, mem_splitPrime, HeightOneSpectrum.mem_adicCompletionIntegers,
    map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 h0)]

theorem exists_isIdemAt_chart : ∀ {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), ∃ e : AE D, IsIdemAt e (GlobalTheory.AdelicU.splitPrime τ) ∧ Chart e v ((GlobalTheory.AdelicU.splitProj τ : Fv D.host.F v ⊗[D.host.F] D.host.E →+* Fv D.host.F v).comp (GlobalTheory.AdelicU.compFin D.host.F D.host.E v)) :=
  fun τ => ⟨idem τ, isIdemAt_idem τ, chart_idem τ⟩

end GlobalTheory.EmbChart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerPadicDeterminantFormula
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FrobStick

open PowerSeries

theorem frobenius_stickelberger_padic_determinant_formula : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicFrobeniusStickelberger D := by
  intro D p _ cc δ g hA
  obtain ⟨hq, hL, h2, h3, hσ, v, hv, hw⟩ := _root_.GlobalTheory.FrobStick.AtData.atData D p cc δ g hA
  have ok : g.Ok := hA.2.2.2.2
  obtain ⟨hAa, hBa, hS, hAv, hBv⟩ := _root_.GlobalTheory.FrobStick.colAB_atU p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hCa, hCv⟩ := GlobalTheory.T.sigmaStarCube_wpDeriv_model_parameter_series GlobalTheory.T.model_parameter_series_deriv_transport p g hq hL h2 h3 hσ v hv hw
  have hF : ∀ j, AlgEnt (![colA g.abelian₂, colB g.abelian₂ v, colC g.abelian₂ v] j) := by
    intro j; fin_cases j
    exacts [hAa, hBa, hCa]
  have h6 := GlobalTheory.T.frobeniusStickelberger_defect_padic_of_complex p g.lam _ (sgStar g.abelian₂) hF hσ (_root_.GlobalTheory.FrobStick.tay_defect_eq_zero _root_.GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines _root_.GlobalTheory.FrobStick.defect_line _root_.GlobalTheory.FrobStick.sgStar_cube_det_cplx g.abelian₂ hL v hv)
  obtain ⟨c0, c1, c2, c3, h7⟩ := _root_.GlobalTheory.FrobStick.SubstLog.subst_log_formula p g ok
  have h8 := h7 ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) _ _ h6
  have e : ∀ F : ℂ → ℂ, (PowerSeries.subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) (GL3Theta.ser1 g.lam F) : PowerSeries ℂ_[p]) = g.atU F :=
    fun F => (GlobalTheory.SerTransport.atU_eq g F).symm
  simp only [e, hS] at h8
  have hw0 : PowerSeries.constantCoeff g.wq = 1 := by
    have h := congrArg PowerSeries.constantCoeff hq
    simpa using h
  refine _root_.GlobalTheory.FrobStick.det_column_ops p (ePhi1 g.lam g.abelian₂ g.C g.wq) g.wq ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) g.C.r g.W.a₁ g.W.a₃ _ _ _ _ (Units.ne_zero _) hw0 c0 c1 c2 c3 ?_
  rw [← h8]
  congr 1
  ext i j
  fin_cases j <;> simp [hAv, hBv, hCv]

end GlobalTheory.FrobStick
end
end

