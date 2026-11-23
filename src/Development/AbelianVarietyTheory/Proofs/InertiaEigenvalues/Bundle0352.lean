module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0263

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachEtaleModuleFrobeniusBasis
section
noncomputable section

namespace GlobalTheory.EtaleFrob

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem linearIndependent_of_span {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}
    (d : Basis (Fin r) R M) (v : Fin r → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    LinearIndependent R v := by
  let f : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R v
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]; exact hv
  let g : (Fin r → R) →ₗ[R] (Fin r → R) := d.equivFun.toLinearMap ∘ₗ f
  have hg : Function.Surjective g := d.equivFun.surjective.comp hf
  have hgi : Function.Injective g := OrzechProperty.injective_of_surjective_endomorphism g hg
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have h1 : g a = g 0 := by
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero, f, Fintype.linearCombination_apply, ha]
  exact fun i => congrFun (hgi h1) i

theorem twmap_smul {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R] [Algebra O R]
    (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (a : R) (z : TW R T) :
    TWmap f T (a • z) = f a • TWmap f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t => simp [TWmap, TensorProduct.smul_tmul', map_mul]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

theorem twmap_surjective {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R] [Algebra O R]
    (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (hf : Function.Surjective f) :
    Function.Surjective (TWmap f T) :=
  TensorProduct.map_surjective (g := f.toLinearMap) hf (g' := LinearMap.id) (fun x => ⟨x, rfl⟩)

end GlobalTheory.EtaleFrob

namespace GlobalTheory.EtaleFrob

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}


set_option maxHeartbeats 1000000 in
theorem phi_basis_of_tie {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) [Nontrivial W.EE] [Nontrivial O]
    (hφ : Function.Surjective φR) (hunits : ∀ x : W.EE, IsUnit (E.ioE x) → IsUnit x)
    (T : LocLat G Qp LL O) (hTfree : Module.Free O ↥T.L.T) (hTfin : Module.Finite O ↥T.L.T) :
    ∃ (r : ℕ) (b b' : Module.Basis (Fin r) W.EE (W.DD T)), ∀ j, b' j = W.φD T (b j) := by
  haveI hfreeD : Module.Free W.EE (W.DD T) := (W.DD_free T).1
  have hrk : finrank W.EE (W.DD T) = finrank O ↥T.L.T := (W.DD_free T).2
  obtain ⟨d0⟩ : Nonempty (Basis (Fin (finrank O ↥T.L.T)) RW (TW RW T)) :=
    ⟨Algebra.TensorProduct.basis RW (Module.finBasis O ↥T.L.T)⟩
  haveI hfin : Module.Finite W.EE (W.DD T) := by
    rcases Nat.eq_zero_or_pos (finrank W.EE (W.DD T)) with h0 | h0
    · haveI : IsEmpty (Fin (finrank O ↥T.L.T)) := by rw [← hrk, h0]; infer_instance
      have hz : ∀ x : W.DD T, x = 0 := fun x => E.jD_inj T (by
        rw [map_zero, ← d0.sum_repr (E.jD T x)]; simp)
      haveI : Subsingleton (W.DD T) := ⟨fun x y => by rw [hz x, hz y]⟩
      infer_instance
    · exact Module.finite_of_finrank_pos h0
  obtain ⟨r, hr⟩ : ∃ r, r = finrank W.EE (W.DD T) := ⟨_, rfl⟩
  obtain ⟨b⟩ : Nonempty (Basis (Fin r) W.EE (W.DD T)) :=
    ⟨(Module.finBasis W.EE (W.DD T)).reindex (finCongr hr.symm)⟩
  obtain ⟨d⟩ : Nonempty (Basis (Fin r) RW (TW RW T)) := ⟨d0.reindex (finCongr (hr.trans hrk).symm)⟩

  obtain ⟨c, hcdef⟩ : ∃ c : Fin r → TW RW T, ∀ j, c j = E.jD T (b j) := ⟨_, fun _ => rfl⟩
  have hjD : ∀ x : W.DD T, E.jD T x = ∑ i, E.ioE (b.repr x i) • c i := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [E.jD_smul, hcdef]
  have hc : Submodule.span RW (Set.range c) = ⊤ := by
    rw [eq_top_iff, ← E.jD_span T, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hjD x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  obtain ⟨cb, hcb⟩ : ∃ cb : Basis (Fin r) RW (TW RW T), ∀ i, cb i = c i :=
    ⟨Basis.mk (linearIndependent_of_span d c hc) hc.ge, fun i => Basis.mk_apply _ _ i⟩

  obtain ⟨c', hc'def⟩ : ∃ c' : Fin r → TW RW T, ∀ j, c' j = TWmap φR T (c j) := ⟨_, fun _ => rfl⟩
  have hTW : ∀ y : TW RW T, ∃ x, TWmap φR T x = y := fun y => twmap_surjective φR T hφ y
  have himg : ∀ x : TW RW T, TWmap φR T x ∈ Submodule.span RW (Set.range c') := by
    intro x
    have hx : x ∈ Submodule.span RW (Set.range c) := by rw [hc]; exact Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun RW).1 hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← ha, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [twmap_smul, ← hc'def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hc' : Submodule.span RW (Set.range c') = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, hxy⟩ := hTW y
    rw [← hxy]
    exact himg x
  have hdet : IsUnit (cb.det c') := cb.is_basis_iff_det.1 ⟨linearIndependent_of_span d c' hc', hc'⟩

  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin r) (Fin r) W.EE, M = b.toMatrix (fun j => W.φD T (b j)) :=
    ⟨_, rfl⟩
  have hM : cb.toMatrix c' = M.map E.ioE := by
    ext i j
    rw [Basis.toMatrix_apply, Matrix.map_apply]
    have e1 : c' j = ∑ k, E.ioE (M k j) • cb k := by
      rw [hc'def, hcdef, ← E.jD_φ, hjD]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcb, hMdef, Basis.toMatrix_apply]
    rw [e1, ← Basis.equivFun_symm_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hdetM : IsUnit (E.ioE M.det) := by
    rw [AlgHom.map_det]
    rw [Basis.det_apply, hM] at hdet
    exact hdet
  have hbas := (b.is_basis_iff_det (v := fun j => W.φD T (b j))).2
    (by rw [Basis.det_apply, ← hMdef]; exact hunits _ hdetM)
  exact ⟨r, b, Basis.mk hbas.1 hbas.2.ge, fun j => Basis.mk_apply _ _ j⟩

end Generic

theorem φRW_onto {l : ℕ} [Fact l.Prime] (LL : FinExt l) : Function.Surjective (φRW LL) := by
  haveI := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  have h : Function.Surjective (frobW l) :=
    WittVector.map_surjective (frobenius (Cb l) l) fun x =>
      IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos
  exact LinearMap.lTensor_surjective ↥(OL LL) (g := (frobW l).toLinearMap) h


set_option maxHeartbeats 1000000 in
theorem phi_basis : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ (r : ℕ) (b b' : Module.Basis (Fin r) W.EE (W.DD T)), ∀ j, b' j = W.φD T (b j) := by
  intro D HW F l _ K s LL h W T
  haveI : Nontrivial W.EE := W.EE_inj.nontrivial
  exact phi_basis_of_tie ((F l).E K s LL h).tie (φRW_onto LL)
    (GlobalTheory.IoInj.ioE_injective_saturated_inter l (D.loc l) (D.locA l) K s LL h _ _ _
      (GlobalTheory.NL.ioW (HW l) (F l) h (GlobalTheory.NL.Holds.laws (HW l) (F l) h))).2.1
    T T.L.free (Module.Finite.iff_fg.mpr T.L.fg)

end GlobalTheory.EtaleFrob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFrobeniusFlatCrystalline
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.PhiFlat

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (y : W.DD T) :
    W.φD T (a • y) = W.φA a • W.φD T y := by
  rw [← algebraMap_smul W.EE a y, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem span_φ (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (bN : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hQ : IsUnit (algebraMap (LetA O n) W.EE W.Q)) :
    Submodule.span W.EE (Set.range fun j => W.φD T (bN j)) = ⊤ := by
  set S := Submodule.span W.EE (Set.range fun j => W.φD T (bN j)) with hS
  have hA : Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) ≤ S.restrictScalars (LetA O n) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y = ∑ m, bN.repr ⟨y, hy⟩ m • (bN m : W.DD T) := by
      have h0 := congrArg Subtype.val (bN.sum_repr ⟨y, hy⟩)
      rw [Submodule.coe_sum] at h0
      simp only [Submodule.coe_smul] at h0
      exact h0.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy', map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [φD_smulA, ← algebraMap_smul W.EE, Submodule.restrictScalars_mem]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self m))
  have hb : ∀ j, (bN j : W.DD T) ∈ S := by
    intro j
    obtain ⟨k, hk⟩ := W.N_φinv T (bN j) (bN j).2
    change W.Q ^ k • (bN j : W.DD T) ∈ _ at hk
    have h1 := hA hk
    rw [Submodule.restrictScalars_mem] at h1
    obtain ⟨u, hu⟩ := hQ.pow k
    have h2 : (bN j : W.DD T) = ((u⁻¹ : W.EEˣ) : W.EE) • (W.Q ^ k • (bN j : W.DD T)) := by
      rw [← algebraMap_smul W.EE (W.Q ^ k), smul_smul, map_pow, ← hu, Units.inv_mul, one_smul]
    rw [h2]
    exact S.smul_mem _ h1
  let bD : Module.Basis (Fin r) W.EE (W.DD T) := (W.N_base T hT).basis bN
  have hbD : ∀ j, bD j = (bN j : W.DD T) := fun j => by simp [bD, IsBaseChange.basis_apply]
  rw [eq_top_iff, ← bD.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [hbD]
  exact hb j

theorem phi_flat (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (bN : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hQ : IsUnit (algebraMap (LetA O n) W.EE W.Q))
    [Nontrivial W.EE] (hr : Module.finrank W.EE (W.DD T) = r) (l : ℕ)
    (hφ₀ : ∀ w : Fin l → PowerSeries O, ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * W.φ₀ (w j) = 0 → w = 0)
    (z : Fin l → W.DD T) (hz : ∀ j, z j ∈ W.N T)
    (hsum : ∑ j : Fin l, (fun _ => ((1 : PowerSeries O) + PowerSeries.X) ^ (j : ℕ) : LetA O n) • W.φD T (z j) = 0) :
    ∀ j, z j = 0 := by
  have hsp := span_φ W T hT bN hQ
  let c : Module.Basis (Fin r) W.EE (W.DD T) :=
    basisOfTopLeSpanOfCardEqFinrank (fun j => W.φD T (bN j)) hsp.ge (by rw [hr, Fintype.card_fin])
  have hli : LinearIndependent W.EE (fun j => W.φD T (bN j)) := by
    have := c.linearIndependent
    rwa [coe_basisOfTopLeSpanOfCardEqFinrank] at this
  set a : Fin l → Fin r → LetA O n := fun j m => bN.repr ⟨z j, hz j⟩ m with ha
  have hzj : ∀ j, z j = ∑ m, a j m • (bN m : W.DD T) := by
    intro j
    have h0 := congrArg Subtype.val (bN.sum_repr ⟨z j, hz j⟩)
    rw [Submodule.coe_sum] at h0
    simp only [Submodule.coe_smul] at h0
    exact h0.symm
  set e : Fin l → LetA O n := fun j => fun _ => ((1 : PowerSeries O) + PowerSeries.X) ^ (j : ℕ) with he
  have hexp : ∑ m, algebraMap (LetA O n) W.EE (∑ j, e j * W.φA (a j m)) • W.φD T (bN m) = 0 := by
    rw [← hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [algebraMap_smul, hzj, map_sum, φD_smulA, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc : ∀ m, ∑ j, e j * W.φA (a j m) = 0 := by
    intro m
    have := Fintype.linearIndependent_iff.1 hli _ hexp m
    exact W.EE_inj (by rw [this, map_zero])
  have hzero : ∀ j m, a j m = 0 := by
    intro j m
    funext k
    have h1 := congrFun (hc m) (k + 1)
    simp only [Finset.sum_apply, Pi.mul_apply, he, LocWach.φA, letφ, AlgHom.pi_apply, AlgHom.comp_apply,
      Pi.evalAlgHom_apply, add_sub_cancel_right, Pi.zero_apply] at h1
    exact congrFun (hφ₀ (fun j => a j m k) h1) j
  intro j
  rw [hzj j]
  simp [hzero]

end Generic

end GlobalTheory.NL.PhiFlat

namespace GlobalTheory.NL.PhiFlat


set_option maxHeartbeats 1600000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ z : Fin l → W.DD T, (∀ j, z j ∈ W.N T) → ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) • W.φD T (z j) = 0 → ∀ j, z j = 0 := by
  intro D HW F l _ K s LL h W T hT z hz hsum
  obtain ⟨bN⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  have hQ : IsUnit (algebraMap (AA K LL) W.EE W.Q) := by
    have := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    rw [pow_zero, AlgHom.one_apply] at this
    exact this
  obtain ⟨χ, -, hφ, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨hdvr, hcpl, hnu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  haveI : Nontrivial W.EE :=
    ⟨⟨algebraMap (AA K LL) W.EE 0, algebraMap (AA K LL) W.EE 1, fun h0 => zero_ne_one (W.EE_inj h0)⟩⟩
  refine GlobalTheory.NL.PhiFlat.phi_flat W T hT bN hQ (W.DD_free T).2 l ?_ z hz hsum
  intro w hw
  obtain ⟨y, -, huniq⟩ := GlobalTheory.Cyc.phi_free l (↥(OL LL)) hl0 hnu 0
  rw [hφ] at hw
  have e1 := huniq w hw.symm
  have e2 := huniq 0 (by simp)
  rw [e1, e2]

end GlobalTheory.NL.PhiFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorMapBreuilKisinEvEq
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem wmap_ev_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O]
    [CharP O l] [PerfectRing O l] (ψ ψ' : OCb l →+* O), ψ bk.flat ≠ 0 →
    IsAdicComplete (Ideal.span {ψ bk.flat}) O →
    (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) →
    ∀ s : bk.S, WittVector.map ψ (bk.ev s) = WittVector.map ψ' (bk.ev s) := by
  intro l _ K bk O _ _ _ _ ψ ψ' h0 hc h s
  have hval : ∀ y : Fq l bk.a, ψ (Fq.val l bk.a y) = ψ' (Fq.val l bk.a y) := fun y => by
    have := h (C (WittVector.teichmuller l y))
    rwa [bk.ev_C, wA_teich, WittVector.teichmuller_coeff_zero] at this
  have hflat : ψ bk.flat = ψ' bk.flat := by
    have := h X
    rwa [bk.ev_X, WittVector.teichmuller_coeff_zero] at this
  have hX : ((WittVector.map ψ).comp bk.ev) X = WittVector.teichmuller l (ψ bk.flat) := by
    rw [RingHom.comp_apply, bk.ev_X, WittVector.map_teichmuller]
  have hcomp := (_root_.GlobalTheory.WittTeichComplete.main l O (ψ bk.flat) h0 hc).1
  refine RingHom.congr_fun (ringHom_ext_of_sep ((WittVector.map ψ).comp bk.ev) ((WittVector.map ψ').comp bk.ev)
    (fun w => ?_) ?_ fun x hx => ?_) s
  · simp only [RingHom.comp_apply, bk.ev_C]
    refine WittVector.ext fun n => ?_
    simp only [wA, AlgHom.coe_mk, WittVector.map_coeff]
    exact hval _
  · rw [hX, RingHom.comp_apply, bk.ev_X, WittVector.map_teichmuller, hflat]
  · rw [hX] at hx
    refine IsHausdorff.haus' (I := Ideal.span {WittVector.teichmuller l (ψ bk.flat)}) x fun n => ?_
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.2 (hx n)

end GlobalTheory.BSP
end
end

