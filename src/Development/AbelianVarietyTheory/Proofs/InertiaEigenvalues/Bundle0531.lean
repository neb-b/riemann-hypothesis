module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateDualLocalGaloisRepAtPlace
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.TateDualX

section Mat

variable {G : Type} [Group G] {LL : Type} [Field LL] {k : ℕ} {V : Type} [AddCommGroup V] [Module LL V]

def toMat (b : Basis (Fin k) LL V) (ρ : Representation LL G V) : G →* Matrix (Fin k) (Fin k) LL :=
  (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp ρ

theorem toMat_apply (b : Basis (Fin k) LL V) (ρ : Representation LL G V) (g : G) :
    toMat b ρ g = LinearMap.toMatrix b b (ρ g) := rfl

def dualTw (c : G →* LLˣ) (M : G →* Matrix (Fin k) (Fin k) LL) : G →* Matrix (Fin k) (Fin k) LL where
  toFun g := ((c g : LLˣ) : LL) • (M g⁻¹).transpose
  map_one' := by simp
  map_mul' g h := by
    simp only [mul_inv_rev, map_mul, Units.val_mul, Matrix.transpose_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, mul_comm]

theorem dualTw_apply (c : G →* LLˣ) (M : G →* Matrix (Fin k) (Fin k) LL) (g : G) :
    dualTw c M g = ((c g : LLˣ) : LL) • (M g⁻¹).transpose := rfl

end Mat

section Cont

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] {k : ℕ}

theorem continuous_dualTw (c : G →* LLˣ) (M : G →* Matrix (Fin k) (Fin k) LL)
    (hc : Continuous fun g => ((c g : LLˣ) : LL)) (hM : Continuous fun g => M g) :
    Continuous fun g => dualTw c M g :=
  hc.smul (hM.comp continuous_inv).matrix_transpose

theorem continuous_toMat {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V]
    [IsModuleTopology LL V] (b : Basis (Fin k) LL V)
    (ρ : Representation LL G V) (hρ : ∀ x, Continuous fun g => ρ g x) :
    Continuous fun g => toMat b ρ g := by
  refine continuous_matrix fun a j => ?_
  have h : Continuous (b.coord a) := IsModuleTopology.continuous_of_linearMap _
  refine (h.comp (hρ (b j))).congr fun g => ?_
  simp [toMat_apply, LinearMap.toMatrix_apply]

end Cont

section Transport

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {k : ℕ}

theorem isDual1_basis (b : Basis (Fin k) LL V) (ρ : Representation LL G V)
    (U : G →* Matrix (Fin k) (Fin k) LL)
    (hd : IsDual1 PD (matRep (toMat b ρ)) (matRep U) (dotProductBilin LL LL)) :
    IsDual1 PD ρ (matRep U) ((dotProductBilin LL LL).comp b.equivFun.toLinearMap) := by
  have hM : ∀ g x, b.equivFun (ρ g x) = matRep (toMat b ρ) g (b.equivFun x) := by
    intro g x
    change _ = (toMat b ρ g).mulVec _
    rw [toMat_apply, Basis.equivFun_apply, Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, ?_⟩
  · change dotProductBilin LL LL (b.equivFun (ρ g x)) (matRep U g y) = _ * dotProductBilin LL LL (b.equivFun x) y
    rw [hM]
    exact hd.1 g (b.equivFun x) y
  · have := hd.2.1 (b.equivFun x) fun y => hx y
    exact b.equivFun.injective (by rw [this, map_zero])
  · refine hd.2.2.1 y fun v => ?_
    have h := hy (b.equivFun.symm v)
    change dotProductBilin LL LL (b.equivFun (b.equivFun.symm v)) y = 0 at h
    rwa [LinearEquiv.apply_symm_apply] at h
  · rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis b, Fintype.card_fin]

end Transport

section Loc

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem continuous_cyc : Continuous fun g : Br.G D.nbr i w hw =>
    ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) :
      Br.LL D.nbr i w hw) := by
  rw [← GlobalTheory.CycBridge.locChi_epsU_eq_cycLL D i w hw]
  have hfc : Continuous (D.nbr i w hw).toLL :=
    continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have hι : Continuous fun g : Br.G D.nbr i w hw => ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)
  exact hfc.comp ((GlobalTheory.Pass.FamCont.epsU_cont D.nd i).comp hι)

end Loc

theorem exists_tateDual : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)),
    ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
      (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
      IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX := by
  intro D i w hw X
  have hU : Continuous fun g => dualTw (cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw))
      (toMat (Module.finBasis (Br.LL D.nbr i w hw) X.V) X.ρ) g :=
    continuous_dualTw _ _ (continuous_cyc D i w hw) (continuous_toMat _ X.ρ X.cont)
  exact ⟨GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ hU, _,
    isDual1_basis (Br.PD D.loc D.nbr i w hw) (Module.finBasis (Br.LL D.nbr i w hw) X.V) X.ρ _
      (GlobalTheory.PotDual.isDual1_of_eq (Br.PD D.loc D.nbr i w hw) _ _ fun g => dualTw_apply _ _ g)⟩

end GlobalTheory.TateDualX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWachImageIsClosed
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology

namespace GlobalTheory.WeakClosedX

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem jD_aN_eq_range_gen {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l}
    {s : ℕ} {LL : FinExt l} {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) (T : Lt K LL) (a : AA K LL) :
    ∃ (r : ℕ) (y : Fin r → TW (RW LL) T), E.tie.jD T '' (aN W T a : Set (W.DD T)) =
      Set.range fun c : Fin r → AA K LL => ∑ i, inclR LL (E.tie.io (c i)) • y i := by
  obtain ⟨S, hS⟩ := W.N_fg T
  let n : Fin S.card → W.DD T := fun i => (S.equivFin.symm i : W.DD T)
  have hrange : Set.range n = (S : Set (W.DD T)) := by
    ext z; constructor
    · rintro ⟨i, rfl⟩; exact (S.equivFin.symm i).2
    · intro hz; exact ⟨S.equivFin ⟨z, hz⟩, by simp [n]⟩
  have hspan : W.N T = Submodule.span (AA K LL) (Set.range n) := by rw [hrange, hS]
  refine ⟨S.card, fun i => E.tie.jD T (a • n i), ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hx
    rw [hspan] at hm
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (AA K LL)).1 hm
    refine ⟨c, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [GlobalTheory.NL.WkRange.jD_smul_letter]
    exact smul_comm _ _ _
  · rintro ⟨c, rfl⟩
    refine ⟨∑ i, c i • (a • n i), ?_, ?_⟩
    · refine Submodule.mem_map.2 ⟨∑ i, c i • n i, ?_, ?_⟩
      · rw [hspan]
        exact (Submodule.mem_span_range_iff_exists_fun (AA K LL)).2 ⟨c, rfl⟩
      · simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum]
        exact Finset.sum_congr rfl fun i _ => GlobalTheory.NL.WkRange.jD_smul_letter E T _ _

theorem jD_XN_closed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X : Set (((HW l).W K s LL h).DD T))) := by
  intro D HW F l _ K s LL h T _
  haveI := LL.2
  haveI : Module.Free ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.2.1
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (LatB T d) := GlobalTheory.Cyc.exists_basis_lat (R := ℤ_[l]) T
  let bO := Module.finBasis ℤ_[l] ↥(OL LL)
  letI τ := twTop T b
  letI tW : TopologicalSpace (WCb l) := wTop l
  letI := cbTop l
  haveI := hausdorff_tilt_witt (l := l)
  haveI := ring_cb (l := l)
  haveI : T2Space (WCb l) := GlobalTheory.WeakTop.t2Space_wittVector_product
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  letI := zlMod T
  haveI := zlTower T
  have hc : Continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) := continuous_induced_dom
  haveI hT2 : T2Space (TW (RW LL) T) :=
    T2Space.of_injective_continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b).injective hc
  haveI hAG : IsTopologicalAddGroup (TW (RW LL) T) :=
    Topology.IsInducing.topologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩
  refine ⟨τ, hT2, hAG, GlobalTheory.T.continuous_galois_orbit_wittTensorLatticeWeakTopology (D.locA l) T b, GlobalTheory.T.continuous_one_tmul_latB T b, ?_⟩
  obtain ⟨r, y, hy⟩ := jD_aN_eq_range_gen ((F l).E K s LL h) T ((HW l).W K s LL h).X
  rw [hy]
  letI := aTop (K := K) bO
  haveI := GlobalTheory.T.compactSpace_aTop' (K := K) bO
  refine (isCompact_range ?_).isClosed
  refine continuous_finsetSum _ fun i _ => ?_
  exact (GlobalTheory.T.continuous_wittCbInclusion_smul_weakTopology ((F l).E K s LL h) T b bO (y i)).comp (continuous_apply i)

end GlobalTheory.WeakClosedX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWildInertiaGeneratingCyclotomicValue
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.WildCycGen

def ex {l : ℕ} (hl : l.Prime) (k : ℕ) : ℕ :=
  (Nat.chineseRemainder (Nat.Coprime.pow_left (k + 1)
    (Nat.coprime_ordCompl hl (Nat.factorial_ne_zero k))) 1 0).1

theorem ex_modEq {l : ℕ} (hl : l.Prime) (k : ℕ) : ex hl k ≡ 1 [MOD l ^ (k + 1)] :=
  (Nat.chineseRemainder (Nat.Coprime.pow_left (k + 1)
    (Nat.coprime_ordCompl hl (Nat.factorial_ne_zero k))) 1 0).2.1

theorem ex_dvd {l : ℕ} (hl : l.Prime) (k : ℕ) :
    (k.factorial / l ^ (k.factorial).factorization l) ∣ ex hl k :=
  Nat.modEq_zero_iff_dvd.1 (Nat.chineseRemainder (Nat.Coprime.pow_left (k + 1)
    (Nat.coprime_ordCompl hl (Nat.factorial_ne_zero k))) 1 0).2.2

theorem pow_ex {Q : Type*} [Group Q] {l : ℕ} (hl : l.Prime) (x : Q) {d : ℕ} (hd : 0 < d)
    (hx : x ^ d = 1) :
    (∀ k, d ≤ k → x ^ ex hl k = x ^ ex hl d) ∧ x ^ (ex hl d * l ^ d.factorization l) = 1 := by
  set a := d.factorization l
  set d' := d / l ^ a
  have hdd : l ^ a * d' = d := Nat.ordProj_mul_ordCompl_eq_self d l
  have hco : (l ^ a).Coprime d' := Nat.Coprime.pow_left a (Nat.coprime_ordCompl hl hd.ne')
  have hla : l ^ a ≤ d := Nat.le_of_dvd hd (Nat.ordProj_dvd d l)
  have ha : a < l ^ a := Nat.lt_pow_self hl.one_lt
  have hdvd : ∀ k, d ≤ k → d' ∣ ex hl k := fun k hk =>
    (Nat.ordCompl_dvd_ordCompl_of_dvd (Nat.dvd_factorial hd hk) l).trans (ex_dvd hl k)
  have hmod1 : ∀ k, d ≤ k → ex hl k ≡ 1 [MOD l ^ a] := fun k hk =>
    Nat.ModEq.of_dvd (Nat.pow_dvd_pow l (by omega)) (ex_modEq hl k)
  have hord : orderOf x ∣ d := orderOf_dvd_of_pow_eq_one hx
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [pow_eq_pow_iff_modEq]
    refine Nat.ModEq.of_dvd hord ?_
    have h := (Nat.modEq_and_modEq_iff_modEq_mul hco).1 ⟨(hmod1 k hk).trans (hmod1 d le_rfl).symm,
      (Nat.modEq_zero_iff_dvd.2 (hdvd k hk)).trans (Nat.modEq_zero_iff_dvd.2 (hdvd d le_rfl)).symm⟩
    rwa [hdd] at h
  · obtain ⟨t, ht⟩ := hdvd d le_rfl
    have e : ex hl d * l ^ a = d * t := by rw [ht, ← hdd]; ring
    rw [e, pow_mul, hx, one_pow]

theorem exists_proL {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {l : ℕ} (hl : l.Prime) (σ : G) : ∃ g0 : G,
    (∀ C : Set G, IsClosed C → (∀ k, σ ^ ex hl k ∈ C) → g0 ∈ C) ∧
    ∀ N : Subgroup G, N.Normal → IsOpen (N : Set G) → ∃ a : ℕ, g0 ^ (l ^ a) ∈ N := by
  obtain ⟨g0, -, hg0⟩ := isCompact_univ.exists_clusterPt
    (f := Filter.map (fun k => σ ^ ex hl k) Filter.atTop) (by simp)
  have hmem : ∀ C : Set G, IsClosed C → (∀ᶠ k in Filter.atTop, σ ^ ex hl k ∈ C) → g0 ∈ C := by
    intro C hC hev
    have h := hg0.mem_closure_of_mem (s := C) hev
    rwa [hC.closure_eq] at h
  refine ⟨g0, fun C hC h => hmem C hC (Filter.Eventually.of_forall h), fun N hN hNo => ?_⟩
  have hfin := Subgroup.quotient_finite_of_isOpen N hNo
  have hd : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hx : ((σ : G ⧸ N)) ^ N.index = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 (N.pow_index_mem σ)
  obtain ⟨h1, h2⟩ := pow_ex hl (σ : G ⧸ N) hd hx
  have hC : IsClosed {τ : G | τ⁻¹ * σ ^ ex hl N.index ∈ N} :=
    (N.isClosed_of_isOpen hNo).preimage (by fun_prop)
  have hg : g0⁻¹ * σ ^ ex hl N.index ∈ N := by
    refine hmem _ hC ?_
    rw [Filter.eventually_atTop]
    refine ⟨N.index, fun k hk => ?_⟩
    show (σ ^ ex hl k)⁻¹ * σ ^ ex hl N.index ∈ N
    rw [← QuotientGroup.eq, QuotientGroup.mk_pow, QuotientGroup.mk_pow]
    exact h1 k hk
  refine ⟨N.index.factorization l, ?_⟩
  have hq : (g0 : G ⧸ N) = (σ : G ⧸ N) ^ ex hl N.index := by
    rw [QuotientGroup.eq.2 hg, QuotientGroup.mk_pow]
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hq, ← pow_mul, h2]

end GlobalTheory.WildCycGen

namespace GlobalTheory.WildCycGen

theorem wild_of_pow {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {l : ℕ} (hl : l.Prime) (hA : A.valuation (l : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {y : Ω} (hy : y ≠ 0) {n : ℕ} (hn : (σ ^ (l ^ n)) y = y) :
    A.valuation (σ y / y - 1) < 1 := by
  have hdec : σ ∈ Dec (F := E) A := hσ.1
  have hvs : ∀ (j : ℕ) (z : Ω), A.valuation ((σ ^ j) z) = A.valuation z := fun j z =>
    GlobalTheory.PrimeToInertia.valuation_apply_eq (pow_mem hdec j) z
  set x := σ y / y with hx
  have hy0 : A.valuation y ≠ 0 := by simpa using hy
  have hx1 : A.valuation x = 1 := by
    rw [hx, map_div₀, show σ y = (σ ^ 1) y by rw [pow_one], hvs 1 y, div_self hy0]
  have hxy : σ y = x * y := by rw [hx]; field_simp
  have hprod : ∀ k : ℕ, (σ ^ k) y = (∏ j ∈ Finset.range k, (σ ^ j) x) * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hxy, map_mul, ih, Finset.prod_range_succ]
      ring
  have hj : ∀ j : ℕ, A.valuation ((σ ^ j) x - x) < 1 := fun j => (pow_mem hσ j).2 x hx1.le
  have hpk : ∀ k : ℕ, A.valuation ((∏ j ∈ Finset.range k, (σ ^ j) x) - x ^ k) < 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, pow_succ]
      have e : (∏ j ∈ Finset.range k, (σ ^ j) x) * (σ ^ k) x - x ^ k * x =
          ((∏ j ∈ Finset.range k, (σ ^ j) x) - x ^ k) * (σ ^ k) x + x ^ k * ((σ ^ k) x - x) := by ring
      rw [e]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul, hvs k x, hx1, mul_one]; exact ih
      · rw [map_mul, map_pow, hx1, one_pow, one_mul]; exact hj k
  have hP : (∏ j ∈ Finset.range (l ^ n), (σ ^ j) x) = 1 := by
    have h := hprod (l ^ n)
    rw [hn] at h
    exact mul_right_cancel₀ hy (h.symm.trans (one_mul y).symm)
  have hxN : A.valuation (x ^ (l ^ n) - 1) < 1 := by
    have h := hpk (l ^ n)
    rw [hP, ← Valuation.map_neg, neg_sub] at h
    exact h

  have hxA : x ∈ A := (A.valuation_le_one_iff x).1 hx1.le
  set xa : A := ⟨x, hxA⟩
  haveI : Fact l.Prime := ⟨hl⟩
  have hlm : ((l : A) : Ω) = (l : Ω) := by simp
  have hl0 : ((l : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff, hlm]
    exact hA
  haveI : CharP (IsLocalRing.ResidueField A) l := (CharP.charP_iff_prime_eq_zero hl).2 hl0
  have h1 : IsLocalRing.residue A (xa ^ (l ^ n) - 1) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    simpa [xa] using hxN
  have h2 : IsLocalRing.residue A (xa - 1) = 0 := by
    rw [map_sub, map_pow, map_one] at h1
    have h3 : (IsLocalRing.residue A xa - 1) ^ (l ^ n) = 0 := by
      rw [sub_pow_char_pow, one_pow, h1]
    rw [map_sub, map_one]
    exact pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero) |>.1 h3
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h2
  simpa [xa] using h2

end GlobalTheory.WildCycGen

namespace GlobalTheory.WildCycGen

theorem one_add_pow_sub_mem {l : ℕ} [Fact l.Prime] {s c : ℕ} (hs : 1 ≤ s) (hc : c % l = 1) :
    (1 + (l : ℤ_[l]) ^ s) ^ c - (1 + (l : ℤ_[l]) ^ s) ∈ Ideal.span {(l : ℤ_[l]) ^ (s + 1)} := by
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
  simp only [map_sub, map_pow, map_add (f := _), map_one, map_natCast]
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  set X : ZMod (l ^ (s' + 1 + 1)) := (l : ZMod (l ^ (s' + 1 + 1))) ^ (s' + 1) with hX
  have hlx : (l : ZMod (l ^ (s' + 1 + 1))) * X = 0 := by
    rw [hX, ← pow_succ', ← Nat.cast_pow, ZMod.natCast_self]
  have hX2 : X * X = 0 := by
    have e : X * X = ((l : ZMod (l ^ (s' + 1 + 1))) * X) * (l : ZMod (l ^ (s' + 1 + 1))) ^ s' := by
      rw [hX]; ring
    rw [e, hlx, zero_mul]
  have hpow : ∀ m : ℕ, (1 + X) ^ m = 1 + (m : ZMod (l ^ (s' + 1 + 1))) * X := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ (1 + X) m, ih]
      push_cast
      linear_combination (m : ZMod (l ^ (s' + 1 + 1))) * hX2
  rw [hpow]
  have hc' : c = l * (c / l) + 1 := by have := Nat.div_add_mod c l; omega
  rw [hc']
  push_cast
  linear_combination ((c / l : ℕ) : ZMod (l ^ (s' + 1 + 1))) * hlx

theorem ex_mod {l : ℕ} (hl : l.Prime) (k : ℕ) : ex hl k % l = 1 := by
  have h := Nat.ModEq.of_dvd (dvd_pow_self l (Nat.succ_ne_zero k)) (ex_modEq hl k)
  rw [Nat.ModEq, Nat.mod_eq_of_lt hl.one_lt] at h
  exact h

theorem main : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∃ g0 : GE D.nd, (∃ w ∈ placesOver D.host.E (D.nd.l i), g0 ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) ∧ (∃ u : ℤ_[D.nd.l i]ˣ, ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) = 1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * (u : ℤ_[D.nd.l i])) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), g0 ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → g0 ∈ wildSet D.nd (D.nd.plOm.1 w) := by
  intro D i k hk
  have hl : (D.nd.l i).Prime := Fact.out

  obtain ⟨w, hw⟩ : (placesOver D.host.E (D.nd.l i)).Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero ?_
    rw [(GlobalTheory.TypeDegOne.degree_one D i k hk).1]
    have h5 : D.R.f = 2 * D.R.ord := rfl
    rw [h5]
    have hord := D.R.toFrame.ord_pos
    positivity
  obtain ⟨σ, hσI, hσc⟩ := GlobalTheory.PtCore.EpsAll.exists_generator (GlobalTheory.EpsInertia.epsAll D i) w hw
  obtain ⟨g0, hC, hP⟩ := exists_proL hl σ
  have hs : 1 ≤ D.nd.s0 i := by
    exact UpperTheory.KStar.S0.one_le_localLevel D.nd i
  refine ⟨g0, ⟨w, hw, hC _ (isClosed_Ine (F := D.host.E) (D.nd.plOm.1 w)) fun k => pow_mem hσI _⟩, ?_, ?_⟩
  ·
    set L : ℤ_[D.nd.l i] := (D.nd.l i : ℤ_[D.nd.l i])
    have hcont : Continuous fun τ : GE D.nd =>
        ‖((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) τ : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) -
          (1 + L ^ D.nd.s0 i)‖ :=
      continuous_norm.comp ((Units.continuous_val.comp (continuous_cycZ _ _ (D.nd.l i))).sub continuous_const)
    have hg := hC _ (isClosed_le hcont continuous_const) fun k => by
      show ‖((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) (σ ^ ex hl k) : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) -
          (1 + L ^ D.nd.s0 i)‖ ≤ ((D.nd.l i : ℝ)) ^ (-((D.nd.s0 i + 1 : ℕ) : ℤ))
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, map_pow, Units.val_pow_eq_pow_val, hσc]
      exact one_add_pow_sub_mem hs (ex_mod hl k)
    rw [Set.mem_setOf_eq, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton'] at hg
    obtain ⟨t, ht⟩ := hg
    have hu : IsUnit (1 + L * t) := by
      rw [← sub_neg_eq_add]
      refine IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h => ?_
      exact PadicInt.irreducible_p.not_isUnit (isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h))
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec]
    linear_combination (-1 : ℤ_[D.nd.l i]) * ht
  ·
    intro w' hw' hine y hy
    have hA : (D.nd.plOm.1 w').valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 := by
      have h := (D.nd.plOm.2 w' ((D.nd.l i : ℕ) : 𝓞 D.host.E)).2 hw'
      simpa using h
    have hfd : FiniteDimensional D.host.E (IntermediateField.adjoin D.host.E {y}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
    have ho := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin D.host.E {y})
    obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
      ⟨Subgroup.isClosed_of_isOpen _ ho, ho⟩ (IntermediateField.adjoin D.host.E {y}).fixingSubgroup.one_mem
    obtain ⟨a, ha⟩ := hP H.toSubgroup H.isNormal' H.isOpen
    have hfix : (g0 ^ (D.nd.l i ^ a)) y = y :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hH ha) y
        (IntermediateField.subset_adjoin _ _ (Set.mem_singleton y))
    exact wild_of_pow hl hA hine hy hfix

end GlobalTheory.WildCycGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsXPowSmulMemWachModuleOfFrobeniusStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_X_pow_smul_mem_wachModule_of_frobenius : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → ∃ a : ℕ, W.X ^ a • m ∈ W.N T := by
  first | exact @GlobalTheory.NL.DenomStep.main | exact GlobalTheory.NL.DenomStep.main | (intros; apply GlobalTheory.NL.DenomStep.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusCongrOfFiniteOfLocalDividedPowerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_congr_of_finite_of_local_dividedPower : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (w : ℕ × ℕ → Wq l a) (s : Finset (ℕ × ℕ)), ofW t K e (fun p => if p ∈ s then w p else 0) ∈ GoodSet t e φ₂) → (∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H))) → (∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (G ^ l)) = coeff n (coeff i (H ^ l))) → ∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.goodSet_of_finite_of_local | exact GlobalTheory.CrysPrism.goodSet_of_finite_of_local | (intros; apply GlobalTheory.CrysPrism.goodSet_of_finite_of_local <;> assumption)
end

