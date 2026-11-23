module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionExistence.LeOneIffOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLocPlace

open GlobalTheory.FinPl GlobalTheory.FinPl.SplitPoint GlobalTheory.IdemModTwo GlobalTheory.SplitChart GlobalTheory.LocMod.SplitCompl Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem conjPl_ne {D : D7} (s : SplitPlace D.host.E) : Formalism.DivisionValues.conjPl s.w ≠ s.w := by
  intro h
  have hm : ∀ x : 𝓞 D.host.E, x ∈ (Formalism.DivisionValues.conjPl s.w).asIdeal ↔
      IsCMField.ringOfIntegersComplexConj D.host.E x ∈ s.w.asIdeal := by
    intro x
    show x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) s.w.asIdeal ↔ _
    have e0 : (Formalism.DivisionValues.cO D.host.E).symm x = IsCMField.ringOfIntegersComplexConj D.host.E x := RingOfIntegers.ext rfl
    rw [Ideal.mem_map_of_equiv]
    refine ⟨fun ⟨y, hy, hxy⟩ => ?_, fun hx => ⟨_, hx, ?_⟩⟩
    · rw [← e0, ← hxy, RingEquiv.symm_apply_apply]; exact hy
    · rw [← e0, RingEquiv.apply_symm_apply]
  have hw : (GlobalTheory.SplitConjPlace.conjSP s).w = s.w := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    rw [GlobalTheory.SplitConjPlace.mem_conj_w, ← hm, h]
  have hv : ∀ x : D.host.E, Valued.v ((s.i.comp (IsCMField.complexConj D.host.E).toAlgHom).toRingHom x) =
      s.w.valuation D.host.E x := by
    intro x
    have h1 := PI.CompAtExist.muV_eq (GlobalTheory.SplitConjPlace.conjSP s) x
    rw [hw] at h1
    exact h1
  obtain ⟨φ, hφc, hφ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.w s.v _ hv
  obtain ⟨c, hc, -, hci⟩ := GlobalTheory.SplitCompl.exists_ringEquiv D.host.E s
  have hg : ∀ y, φ (c y) = y := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield D.host.E) s.v).induction_on
      (p := fun y => φ (c y) = y) y (isClosed_eq (hφc.comp hc) continuous_id) fun a => ?_
    have e1 := s.i.commutes a
    rw [← e1, hci, hφ]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_algHom]
    rw [AlgEquiv.commutes]
  apply IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => s.i.toRingHom.injective ?_
  have h2 := hg (s.i x)
  rw [hci, hφ] at h2
  exact h2

theorem exists_transport {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (v1 : HeightOneSpectrum (𝓞 F1)) (w : HeightOneSpectrum (𝓞 F2))
    (hv : ∀ a : F1, v1.valuation F1 a = w.valuation F2 ⟨a, h.le a.2⟩) :
    ∃ κ : v1.adicCompletion F1 →+* w.adicCompletion F2, Continuous κ ∧
      (∀ a : F1, κ (algebraMap F1 _ a) = algebraMap F2 (w.adicCompletion F2) ⟨a, h.le a.2⟩) ∧
      ∀ z : FiniteAdeleRing (𝓞 F1) F1, ∃ z' : FiniteAdeleRing (𝓞 F2) F2,
        Formalism.IndefR.principalLevelFrame.tensCastR h (z ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] z' ∧ κ (z v1) = z' w := by
  subst h
  have hvw : v1 = w := by
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F1), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F1),
      hv]
  subst hvw
  exact ⟨RingHom.id _, continuous_id, fun a => rfl, fun z => ⟨z, rfl, rfl⟩⟩

theorem tensCastR_one_tmul {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (x : E) :
    Formalism.IndefR.principalLevelFrame.tensCastR h ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x) = x ⊗ₜ[F2] (1 : FiniteAdeleRing (𝓞 F2) F2) := by
  subst h
  rfl


set_option maxHeartbeats 1000000 in
theorem exists_place : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E),
    ∃ (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E))
      (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E),
      Formalism.L2.JoinChr.IsPlIdem D p.e s.w ∧ Continuous c ∧
      (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧
      ∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a))) := by
  intro D s hF
  obtain ⟨e, he⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conjPl_ne s)
  obtain ⟨-, -, v, ε, hε, hs⟩ := he.1
  have hsa : SplitAt D v e := splitAt_of he.1 hε hs
  have hP := splitPrime_emb hsa s.w he
  have hf : ∀ x : D.host.E, Valued.v ((emb hsa).toRingHom x) = s.w.valuation D.host.E x := by
    intro x
    rw [← hP]
    exact GlobalTheory.AdelicU.valued_apply_eq_valuation (emb hsa) x
  obtain ⟨φ, hφc, hφ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.w v _ hf
  let g : D.host.F →+* s.w.adicCompletion D.host.E :=
    (algebraMap D.host.E (s.w.adicCompletion D.host.E)).comp (algebraMap D.host.F D.host.E)
  have hg : ∀ a, Valued.v (g a) = v.valuation D.host.F a := by
    intro a
    simp only [g, RingHom.comp_apply]
    rw [GlobalTheory.Idele.valued_algebraMap, ← hf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      GlobalTheory.Idele.valued_algebraMap]
  obtain ⟨ψ, hψc, hψ, -⟩ := GlobalTheory.DenseCompl.exists_extension v s.w g hg
  have hcomp : ∀ y, φ (ψ y) = y := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap D.host.F v).induction_on
      (p := fun y => φ (ψ y) = y) y (isClosed_eq (hφc.comp hψc) continuous_id) fun a => ?_
    rw [hψ]
    simp only [g, RingHom.comp_apply]
    rw [hφ]
    exact (emb hsa).commutes a
  let e0 := RingEquiv.ofBijective φ ⟨φ.injective, fun y => ⟨ψ y, hcomp y⟩⟩
  have he0 : ∀ y, e0.symm y = ψ y := fun y => e0.injective (by rw [e0.apply_symm_apply]; exact (hcomp y).symm)
  have hΦc : Continuous e0.symm := hψc.congr fun y => (he0 y).symm
  have hΦc' : Continuous e0 := hφc
  have hΦ : ∀ x : D.host.E, e0.symm (emb hsa x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x := by
    intro x
    have h1 := e0.symm_apply_apply (algebraMap D.host.E (s.w.adicCompletion D.host.E) x)
    exact (congrArg e0.symm (hφ x)).symm.trans h1
  obtain ⟨c, hc, -, hci⟩ := GlobalTheory.SplitCompl.exists_ringEquiv D.host.E s
  have hvv : ∀ a : D.host.F, v.valuation D.host.F a =
      s.v.valuation (maximalRealSubfield D.host.E) ⟨a, hF.le a.2⟩ := by
    intro a
    have h1 := hf (algebraMap D.host.F D.host.E a)
    have h2 := PI.CompAtExist.muV_eq s (algebraMap (maximalRealSubfield D.host.E) D.host.E ⟨a, hF.le a.2⟩)
    rw [← GlobalTheory.Idele.valued_algebraMap, ← GlobalTheory.Idele.valued_algebraMap, ← (emb hsa).commutes, ← s.i.commutes]
    exact h1.trans h2.symm
  obtain ⟨κ, hκc, hκa, hκz⟩ := exists_transport hF v s.v hvv
  have hΦκ : ∀ y, e0.symm y = c (κ y) := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap D.host.F v).induction_on
      (p := fun y => e0.symm y = c (κ y)) y (isClosed_eq hΦc (hc.comp hκc)) fun a => ?_
    have h1 : algebraMap D.host.F (v.adicCompletion D.host.F) a = emb hsa (algebraMap D.host.F D.host.E a) :=
      ((emb hsa).commutes a).symm
    have h2 : algebraMap (maximalRealSubfield D.host.E) (s.v.adicCompletion (maximalRealSubfield D.host.E))
        ⟨a, hF.le a.2⟩ = s.i (algebraMap (maximalRealSubfield D.host.E) D.host.E ⟨a, hF.le a.2⟩) :=
      (s.i.commutes _).symm
    rw [hκa]
    rw [h2]
    rw [hci]
    rw [h1]
    rw [hΦ]
  let p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E) :=
    { e := e
      split := he.1
      π := e0.symm.toRingHom.comp (comp hsa)
      ι := (sec D v e).comp e0.toRingHom.toAddMonoidHom
      π_ι := fun x => by
        show e0.symm (comp hsa (sec D v e (e0 x))) = x
        rw [comp_sec, RingEquiv.symm_apply_apply]
      ι_π := fun a => by
        show sec D v e (e0 (e0.symm (comp hsa a))) = e * a
        rw [RingEquiv.apply_symm_apply, sec_comp]
      cont_π := hΦc.comp (continuous_comp hsa)
      cont_ι := continuous_sec.comp hΦc' }
  refine ⟨p, c, ⟨he.1.1, ⟨v, ε, hε, Or.inl ⟨he.1.2.1, hs⟩⟩, he.2⟩, hc, hci, fun a => ?_⟩
  show e0.symm (comp hsa a) = _
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul y x =>
    have hyx : y ⊗ₜ[D.host.F] x = algebraMap (AF D.host.F) (AE D) y * incA D x := by
      show _ = (y ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hyx, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
    congr 1
    · rw [comp_algebraMap, hΦκ]
      obtain ⟨z', hz1, hz2⟩ := hκz y.2
      have e1 : Formalism.L2.Theta.finPart D (algebraMap (AF D.host.F) (AE D) y) = y.2 ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
      rw [e1]
      show _ = c (s.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF (y.2 ⊗ₜ[D.host.F] (1 : D.host.E))))
      rw [hz1]
      show c (κ (y.2 v)) = c (s.i 1 * z' s.v)
      rw [map_one, one_mul, hz2]
    · show e0.symm (emb hsa x) = _
      rw [hΦ]
      have e1 : Formalism.L2.Theta.finPart D (incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := rfl
      rw [e1]
      show _ = c (s.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF ((1 : Af D.host.F) ⊗ₜ[D.host.F] x)))
      rw [tensCastR_one_tmul]
      show _ = c (s.i x * ReciprocityTheory.Aut.evalAt D.host.E s.v 1)
      rw [map_one, mul_one, hci]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end GlobalTheory.SplitLocPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitRescaledLatticeAndDual
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
open Filter Topology

namespace GlobalTheory.LatChoiceSplit

theorem mem_half_iff {D : D7} {S T : HSp D} (e : AE D) (u : WO S T) : u ∈ half S T e ↔ IsHalf e u := by
  change e • u = u ↔ _
  rw [← Matrix.ext_iff]
  rfl

theorem nhdsNE_neBot (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

theorem isCompact_int_mat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Y Y' : Type) [Fintype Y] [Fintype Y'] : IsCompact {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]} := by
  have : {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]} = Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k) := by
    ext x
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1

theorem exists_smul_int_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Y Y' : Type) [Fintype Y] [Fintype Y'] (A : Set (Matrix Y Y' k)) (hA : IsOpen A) (h0 : (0 : Matrix Y Y' k) ∈ A) :
    ∃ c : k, c ≠ 0 ∧ ∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → c • x ∈ A := by
  have hev : ∀ᶠ c in 𝓝 (0 : k), ∀ x ∈ {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]}, c • x ∈ A := by
    refine (isCompact_int_mat k Y Y').eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : k × Matrix Y Y' k => z.1 • z.2 := continuous_fst.smul continuous_snd
    have : (fun z : k × Matrix Y Y' k => z.1 • z.2) (0, y) ∈ A := by simpa using h0
    exact hc.continuousAt.preimage_mem_nhds (hA.mem_nhds this)
  haveI := nhdsNE_neBot k
  obtain ⟨c, hc1, hc2⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := {(0 : k)}ᶜ))).and (self_mem_nhdsWithin (s := {(0 : k)}ᶜ))).exists
  exact ⟨c, hc2, fun x hx => hc1 x hx⟩

theorem natCast_smul {D : D7} {S T : HSp D} (N : ℕ) (x : WO S T) : (N : AE D) • x = N • x :=
  Nat.cast_smul_eq_nsmul _ _ _

theorem symplO_nsmul_swap {D : D7} (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T (N • x) y = symplO S T x (N • y) := by
  rw [← natCast_smul, GlobalTheory.PlaceModel.symplO_smul, map_natCast, natCast_smul]

theorem psi_neg_eq_one {F : Type} [AddGroup F] (ψ : AddChar F ℂ) (z : F) (h : ψ z = 1) : ψ (-z) = 1 := by
  have := AddChar.map_add_eq_mul ψ z (-z)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, one_mul] at this
  exact this.symm

theorem nsmul_inv_smul {D : D7} {S T : HSp D} {N : ℕ} (hN : 0 < N) (t : WO S T) :
    N • ((incA D (N : D.host.E)⁻¹) • t) = t := by
  rw [smul_comm]
  exact GlobalTheory.PlaceModel.inv_smul_nsmul S T hN t

theorem isHalf_nsmul {D : D7} {m n : ℕ} {e : AE D} {u : Mx D m n} (h : IsHalf e u) (N : ℕ) : IsHalf e (N • u) := by
  intro i j
  show e * (N • u i j) = N • u i j
  rw [nsmul_eq_mul, mul_left_comm, h i j]

theorem isHalf_smul_idem {D : D7} {m n : ℕ} {e : AE D} (he : e * e = e) (w : AE D) (a : Mx D m n) :
    IsHalf e (w • (e • a)) := by
  intro i j
  show e * (w * (e * a i j)) = w * (e * a i j)
  rw [mul_left_comm, ← mul_assoc e e, he]


open GlobalTheory.LocMod.Witness in
theorem exists_split_lattices : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ (U : AddSubgroup (Formalism.IndefR.Datum.WO S T)), IsOpen (U : Set (Formalism.IndefR.Datum.WO S T)) → ∃ c : k, c ≠ 0 ∧ ∃ L' K : AddSubgroup (Formalism.IndefR.Datum.WO S T), (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → p.up FS FT (c • x) ∈ L' ∧ p.up FS FT (c • x) ∈ U) ∧ (∀ t ∈ L', Formalism.IndefR.Datum.IsHalf p.e t) ∧ (∀ y ∈ K, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y ∧ y ∈ U) ∧ (∃ R : Finset (Formalism.IndefR.Datum.WO S T), ∀ t ∈ L', ∃ r ∈ R, ∃ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) ∧ t - r = p.up FS FT (c • x)) ∧ (∀ x ∈ L', ∀ y ∈ K, ψ (Formalism.IndefR.Datum.symplO S T x y) = 1) ∧ (∀ y, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y → (∀ x ∈ L', ψ (Formalism.IndefR.Datum.symplO S T x y) = 1) → y ∈ K) := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ U hU
  classical
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  set Λ₀ := latO S T (GlobalTheory.PlaceModel.latFrame S : Set _) (GlobalTheory.PlaceModel.latFrame T : Set _) (fun _ => True) with hΛ₀
  obtain ⟨N, hN, hNU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T _ _ hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T _ _ hS hT)).1 U hU
  have he : p.e * p.e = p.e := p.split.1
  have hinfe : infPart D p.e = 0 := GlobalTheory.PlaceCoord.infPart_split p.split
  have hinfe' : infPart D (cA D p.e) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinfe
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hNk : (N : k) ≠ 0 := by
    intro h0
    have h1 : (N : AE D) * incA D ((N : D.host.E)⁻¹) = 1 := by
      rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
    have h2 := congrArg p.π h1
    rw [map_mul, map_natCast, h0, zero_mul, map_one] at h2
    exact zero_ne_one h2
  obtain ⟨c, hc0, hc⟩ := exists_smul_int_mem k Y Y'
    (((Λ₀.comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) ∩ ((U.comap (upH p FS FT) : AddSubgroup _) : Set _))
    ((lat_open p FS FT hS hT).inter (hU.preimage (up_cont p FS FT)))
    ⟨zero_mem (Λ₀.comap (upH p FS FT)), zero_mem (U.comap (upH p FS FT))⟩
  let L' : AddSubgroup (WO S T) := half S T p.e ⊓ Λ₀.comap (nsmulAddMonoidHom N)
  let K : AddSubgroup (WO S T) := (Λ₀ ⊓ half S T (cA D p.e)).map (nsmulAddMonoidHom N)
  have hL' : ∀ t, t ∈ L' ↔ IsHalf p.e t ∧ N • t ∈ Λ₀ := fun t => by
    rw [AddSubgroup.mem_inf, mem_half_iff]; rfl
  have hK : ∀ y, y ∈ K ↔ ∃ b, (b ∈ Λ₀ ∧ IsHalf (cA D p.e) b) ∧ N • b = y := fun y => by
    simp only [K, AddSubgroup.mem_map, AddSubgroup.mem_inf, mem_half_iff, nsmulAddMonoidHom_apply]
  refine ⟨c, hc0, L', K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hc x hx
    exact ⟨(hL' _).2 ⟨up_half p FS FT _, nsmul_mem (show p.up FS FT (c • x) ∈ Λ₀ from h1) N⟩, h2⟩
  · exact fun t ht => ((hL' t).1 ht).1
  · intro y hy
    obtain ⟨b, ⟨hb1, hb2⟩, rfl⟩ := (hK y).1 hy
    exact ⟨isHalf_nsmul hb2 N, hNU b hb1⟩
  · have hAc := lat_compact p FS FT hS hT
    have hB : IsCompact ((fun m => (N : k)⁻¹ • m) '' ((Λ₀.comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k))) :=
      hAc.image (continuous_const_smul _)
    have hint : IsOpen {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]} := by
      have : {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]} =
          ⋂ i, ⋂ j, (fun x : Matrix Y Y' k => x i j) ⁻¹' (𝒪[k] : Set k) := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (Valuation.isOpen_integer (v := valuation k)).preimage ((continuous_apply j).comp (continuous_apply i))
    have hVo : IsOpen ((fun m : Matrix Y Y' k => c⁻¹ • m) ⁻¹' {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]}) :=
      hint.preimage (continuous_const_smul _)
    obtain ⟨G, hG⟩ := compact_covered_by_add_left_translates hB
      (V := (fun m : Matrix Y Y' k => c⁻¹ • m) ⁻¹' {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]})
      ⟨0, by rw [hVo.interior_eq]; intro i j; simp⟩
    refine ⟨G.image (fun g => p.up FS FT (-g)), fun t ht => ?_⟩
    obtain ⟨h1, h2⟩ := (hL' t).1 ht
    have hm : N • p.down FS FT t ∈ ((Λ₀.comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) := by
      change upH p FS FT (N • p.down FS FT t) ∈ Λ₀
      rw [map_nsmul]
      change N • p.up FS FT (p.down FS FT t) ∈ Λ₀
      rw [up_down p FS FT h1]
      exact h2
    have hmB : p.down FS FT t ∈ (fun m => (N : k)⁻¹ • m) '' ((Λ₀.comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) :=
      ⟨_, hm, by simp only; rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hNk, one_smul]⟩
    have hG' := hG hmB
    rw [Set.mem_iUnion₂] at hG'
    obtain ⟨g, hg, hgV⟩ := hG'
    refine ⟨p.up FS FT (-g), Finset.mem_image_of_mem _ hg, c⁻¹ • (g + p.down FS FT t), hgV, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    have h3 := up_add p FS FT (-g) (g + p.down FS FT t)
    rw [neg_add_cancel_left, up_down p FS FT h1] at h3
    exact sub_eq_of_eq_add' h3
  · intro x hx y hy
    obtain ⟨h1, h2⟩ := (hL' x).1 hx
    obtain ⟨b, ⟨hb1, -⟩, rfl⟩ := (hK y).1 hy
    rw [← symplO_nsmul_swap]
    have hhalf : IsHalf p.e (N • x) := isHalf_nsmul h1 N
    exact (hdual (N • x) (GlobalTheory.PlaceDatum.infPart_of_half hinfe hhalf)).1 h2 b hb1
  · intro y hy hyL
    obtain ⟨y', hy'h, rfl⟩ := GlobalTheory.PlaceModel.half_div S T (cA D p.e) N hN y ((mem_half_iff _ _).2 hy)
    have hy'h' := (mem_half_iff _ _).1 hy'h
    refine (hK _).2 ⟨y', ⟨?_, hy'h'⟩, rfl⟩
    refine (hdual y' (GlobalTheory.PlaceDatum.infPart_of_half hinfe' hy'h')).2 fun a ha => ?_
    rw [GlobalTheory.PlaceModel.symplO_skew]
    refine psi_neg_eq_one ψ _ ?_
    have hea : p.e • a ∈ Λ₀ := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ p.e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])) a ha
    have hNx : N • (incA D ((N : D.host.E)⁻¹) • (p.e • a)) = p.e • a := nsmul_inv_smul hN _
    have hx : incA D ((N : D.host.E)⁻¹) • (p.e • a) ∈ L' := by
      exact (hL' _).2 ⟨isHalf_smul_idem he _ a, by rw [hNx]; exact hea⟩
    have h4 := hyL _ hx
    rw [← symplO_nsmul_swap, hNx, GlobalTheory.PlaceModel.symplO_smul] at h4
    have hcy : cA D p.e • y' = y' := hy'h
    rwa [hcy] at h4

end GlobalTheory.LatChoiceSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumDependsOnlyAtBadPlacesMatrixStep
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)

noncomputable section

namespace GlobalTheory.AwayMat
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem levOne_of_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := GlobalTheory.T.congruentOne_mem_stepLevel_levelChar_eq_one

theorem muAt_det_of_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ) (P : rowSG Pr sel mu) (n : ℕ) (k : Sp X.E n ≃ₗ[X.E] Sp X.E n),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E n) l))) →
    muAt Ch sel mu cst i P ((LinearEquiv.det k : X.Eˣ) : X.E) = 1 := _root_.GlobalTheory.AwayMat.muAt_det_congr_one

theorem xiAt_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ), i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N i) ≃ₗ[X.E] Sp X.E (R.N i)) (k' : Sp X.E (R.N (i + 1)) ≃ₗ[X.E] Sp X.E (R.N (i + 1))),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N i)) l))) →
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k' (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N (i + 1))) l))) →
    ∀ x, XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (inFr k k' x) = XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hCh hsel hL i hi al be P k k' hk hk' x
  obtain ⟨r, hr, hrk, hc⟩ := levOne_of_cong Ch sel mu cst L G m2 hX hPr hCh hsel hL i hi.le al P k hk
  obtain ⟨r', hr', hrk', hc'⟩ := levOne_of_cong Ch sel mu cst L G m2 hX hPr hCh hsel hL (i + 1) hi be P k' hk'
  have h := GlobalTheory.UnfoldTwoSided.xiAt_two_sided Ch sel mu cst L G m2 hX hPr hCh hsel hL i hi al be P r r' k k' hr hr' hrk hrk' x
  rw [hc, hc', muAt_det_of_cong Ch sel mu cst L G m2 hX hPr hsel hL i P _ k hk, muAt_det_of_cong Ch sel mu cst L G m2 hX hPr hsel hL i P _ k' hk'] at h
  simpa only [one_mul] using h

theorem decoAtT_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    p₁.deco.1.at P.1 = p.deco.1.at P.1 ∧ ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y := fun A dtU a H T i hi β x x₁ p p₁ h1 h2 P hv => ⟨GlobalTheory.T.localizedLattice_eq_of_adelic_matrices_agree_at_place A dtU a H T i hi β x x₁ p p₁ h1 h2 P hv, GlobalTheory.T.chartFunctional_eq_of_agree_under_levelPrime A dtU a H T i hi β x x₁ p p₁ h1 h2 P hv⟩

theorem frames_cong : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : SB t μ,
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∃ k : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i), frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k ∧
      ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) l)) := GlobalTheory.T.chainChart_frames_badPrime_congruent_one_of_adelic_agree

theorem inFr_mul {E : Type} [Field E] {n n' : ℕ} (f k : Sp E n ≃ₗ[E] Sp E n) (f' k' : Sp E n' ≃ₗ[E] Sp E n') (z : HomE E n n') :
    inFr (f * k) (f' * k') z = inFr k k' (inFr f f' z) := LinearMap.ext fun _ => rfl

theorem ptAway_mat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i < t.m2 → PtAway A a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H T i hi him
  intro β β' x x' x₁ x₁' p p' p₁ p₁' h1 h2 h3 h4 hag
  classical
  have hSS : (t.rd u μ).SS = Sall t.sel (t.tup μ) (t.word u) := ((isChainTop_iff _ _ _ _ _ _ _ _ _).1 T.isChainTop).1
  have hv : ∀ Q, Q ∈ Sall t.sel (t.tup μ) (t.word u) → ∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam Q) →
      bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 ∧ bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1 :=
    fun Q hQ v hvQ => hag v ⟨seamP t.seam Q, (mem_ssRec t u μ Q).2 (hSS ▸ hQ), hvQ⟩
  have hX : t.X.AbelianUnramifiedExtensionConditions := H.fields
  have hCh : t.Ch.Ok := H.ch.ch_ok
  have hL := t.idx_ok μ
  funext z
  unfold xiPt
  rw [dite_eq_left him, dite_eq_left him]
  unfold XiEntry
  refine congrArg₂ (· * ·) ?_ ?_
  · have eA := fun P : t.Pr.vT (t.word u) => decoAtT_eq A dtU a H T i _ β x x₁ p p₁ h1 h3 P
      (fun v hv' => (hv P.1 (Finset.mem_union_left _ P.2) v hv').1)
    have eA' := fun P : t.Pr.vT (t.word u) => decoAtT_eq A dtU a H T (i + 1) hi β' x' x₁' p' p₁' h2 h4 P
      (fun v hv' => (hv P.1 (Finset.mem_union_left _ P.2) v hv').2)
    have key : (∀ P : t.Pr.vT (t.word u), ∀ y ∈ p₁.deco.1.at P.1, z y ∈ p₁'.deco.1.at P.1 ∧ p₁'.deco.1.f P (z y) = p₁.deco.1.f P y) ↔
        (∀ P : t.Pr.vT (t.word u), ∀ y ∈ p.deco.1.at P.1, z y ∈ p'.deco.1.at P.1 ∧ p'.deco.1.f P (z y) = p.deco.1.f P y) := by
      refine forall_congr' fun P => ?_
      obtain ⟨a1, f1⟩ := eA P
      obtain ⟨a2, f2⟩ := eA' P
      rw [a1, a2]
      refine forall₂_congr fun y hy => and_congr_right fun hzy => ?_
      rw [f1 y hy, f2 _ hzy]
    unfold phiT
    by_cases hc : ∀ P : t.Pr.vT (t.word u), ∀ y ∈ p.deco.1.at P.1, z y ∈ p'.deco.1.at P.1 ∧ p'.deco.1.f P (z y) = p.deco.1.f P y
    · rw [if_pos hc, if_pos (key.2 hc)]
    · rw [if_neg hc, if_neg (fun h => hc (key.1 h))]
  · refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨k, hk, hkc⟩ := frames_cong A dtU a H T i _ β x x₁ p p₁ h1 h3 P
      (fun v hv' => (hv P.1 (Finset.mem_union_right _ P.2) v hv').1)
    obtain ⟨k', hk', hkc'⟩ := frames_cong A dtU a H T (i + 1) hi β' x' x₁' p' p₁' h2 h4 P
      (fun v hv' => (hv P.1 (Finset.mem_union_right _ P.2) v hv').2)
    rw [hk, hk', inFr_mul]
    exact xiAt_cong t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hX t.pr_ok hCh H.sel hL i him _ _ P k k' hkc hkc' _

end GlobalTheory.AwayMat
end
end

