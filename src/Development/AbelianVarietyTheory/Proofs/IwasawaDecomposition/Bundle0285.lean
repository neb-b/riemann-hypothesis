module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransferOfFundamentalDomains
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartAtUpdSReFace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem lamN_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (kap : ℝ)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) {p} (hp : R.EEp3 p ≠ ⊥) (t j) :
    (R.updS kap (zeroLam R F c)).lamN t j p = R.lamN t j p := by
  unfold RealDat3.lamN
  split_ifs with h
  · exact scalarsZeroPartConvention_fixedPlace R F c ((hZ p hp _).1)
  · rfl

theorem isKap_congr {N Tup Sig : Type} [AddCommGroup N] [Module ℂ N] {m : ℕ} {dnup : Tup → N →ₗ[ℂ] N} {partE : Sig → Submodule ℂ N}
    {lam lam' : Tup → ℕ → Sig → ℝ} {κ : ℝ} (h : Lift.IsKap m dnup partE lam κ)
    (hl : ∀ μ j σ, partE σ ≠ ⊥ → lam' μ j σ = lam μ j σ) : Lift.IsKap m dnup partE lam' κ := by
  intro μ σ x hx
  by_cases hσ : partE σ = ⊥
  · rw [hσ, Submodule.mem_bot] at hx
    subst hx
    simp
  · rw [Finset.prod_congr rfl fun j _ => hl μ j σ hσ]
    exact h μ σ x hx

theorem isLamP_congr {A Amb Sig : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb] {thW : A →ₗ[ℂ] Amb}
    {adj : Amb →ₗ[ℂ] A} {part : Sig → Submodule ℂ Amb} {lam lam' : Sig → ℝ} (h : Lift.IsLamP thW adj part lam)
    (hl : ∀ σ, part σ ≠ ⊥ → lam' σ = lam σ) : Lift.IsLamP thW adj part lam' := by
  intro σ x hx
  by_cases hσ : part σ = ⊥
  · rw [hσ, Submodule.mem_bot] at hx
    subst hx
    simp
  · rw [hl σ hσ]
    exact h σ x hx


set_option maxHeartbeats 1000000 in
theorem thmB_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v)
    (hB : R.PThmB) : (R.updS R.kap (zeroLam R F c)).PThmB := by
  have h := isKap_congr (lam' := (R.updS R.kap (zeroLam R F c)).lamN) hB
    fun μ j σ hσ => lamN_zeroLam R F c R.kap hZ hσ μ j
  exact (by with_unfolding_all exact (h :))


set_option maxHeartbeats 1000000 in
theorem thmA_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hA : R.PThmA) : (R.updS R.kap (zeroLam R F c)).PThmA := by
  have h := fun i t => isLamP_congr (lam' := fun p => zeroLam R F c i t p A3.A.v0) (hA i t)
    fun σ hσ => scalarsZeroPartConvention_fixedPlace R F c hσ
  exact (by with_unfolding_all exact (h :))


set_option maxHeartbeats 1000000 in
theorem galD_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hG : (R.toCx3 F).GalD F.cr false) : ((R.updS R.kap (zeroLam R F c)).toCx3 F).GalD F.cr false := by
  have h := cx_galD_scal (R.toCx3 F) F.cr (fun _ => R.kap) (zeroLam R F c) (fun j p v hv hp => zeroLam_off R F c hv hp) hG
  exact (by with_unfolding_all exact (h :))

theorem partAt_updS_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (i p v) :
    (R.updS kap lam).PartAt (reFace F Dc Sp Zsc) i p v ↔ R.PartAt F i p v :=
  (RealDat3.partAt_updS kap lam i p v).trans Iff.rfl


set_option maxHeartbeats 4000000 in
theorem scal_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v)
    (hs : R.IsScal F) :
    (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)).IsScal (reFace F Dc Sp Zsc) := by
  refine ⟨fun i t p l hp hl => ?_, fun κ hk hne => ?_, fun i p v l hv hp he => ?_, fun i t p hp => ?_,
    fun i p v hv hp => ?_, fun i t p v hv => ?_⟩
  · exact (scalarsZeroPartConvention_fixedPlace R F _ hp).trans (hs.lam0 i t p l hp hl)
  · refine hs.kap κ (fun μ σ x hx => ?_) ?_
    · by_cases hσ : R.EEp3 σ = ⊥
      · rw [hσ, Submodule.mem_bot] at hx
        subst hx
        simp
      · have e := hk μ σ x hx
        rw [Finset.prod_congr rfl fun j _ => lamN_zeroLam R F _ R.kap hZ hσ μ j] at e
        exact e
    · obtain ⟨t, p, hp, hne⟩ := hne
      exact ⟨t, p, hp, by rwa [Finset.prod_congr rfl fun j _ => lamN_zeroLam R F _ R.kap hZ hp t j] at hne⟩
  · have hp' : R.PartAt F i p v := (partAt_updS_reFace R F _ _ Dc Sp Zsc i p v).1 hp
    exact (zeroLam_off R F _ hv hp').trans (hs.off i p v l hv hp' he)
  · exact zeroLam_of_zero R F _ (Or.inl ⟨rfl, hp⟩)
  · exact zeroLam_of_zero R F _ (Or.inr ⟨hv, fun h => hp ((partAt_updS_reFace R F _ _ Dc Sp Zsc i p v).2 h)⟩)
  · show zeroLam R F _ i t p v = zeroLam R F _ i A3.A.μ0 p v
    unfold zeroLam
    split_ifs with h
    · rfl
    · exact hs.tup i t p v hv

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProjectedLift

open Formalism.IndefR.Lev


open scoped Pointwise in
theorem not_isConjPl {D : D7} (P : Formalism.L2.Host.PiBar D.host) {k k' : Fin 2} {w w' : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : P.Div k w) (hw' : P.Div k' w') : ¬ Lev.IsConjPl w w' := by
  intro hc
  have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hz, hzv⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext
      ((hzv.trans (bridge_star_holds D.R D.host _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
    exact e ▸ hz
  obtain ⟨v, hv, -⟩ := GlobalTheory.Mem.Chr.existsUnique_conjPl D.host.conj.toRingEquiv w
  have hv' := (GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj w v).1 hv
  have hvw : v = w' := HeightOneSpectrum.ext (v.isMaximal.eq_of_le w'.isPrime.ne_top (hv' ▸ hle))
  subst hvw
  obtain ⟨ho, hiff⟩ := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w
    (P.overP hw)).2.2.2 (P.pb k) (P.pb_over k) v hv
  have hk : k = k' := by
    by_contra hne
    have hg : D.host.g k ≠ D.host.g k' := by
      fin_cases k <;> fin_cases k'
      · exact absurd rfl hne
      · exact D.host.g_ne
      · exact D.host.g_ne.symm
      · exact absurd rfl hne
    obtain ⟨s, t, hst⟩ : IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) ((D.host.g k' : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime k) (D.host.g_prime k')).2 hg)
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hst]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ ho) (v.asIdeal.mul_mem_left _ (P.overP hw'))
  subst hk
  exact hiff.1 hw hw'

theorem conv_of_idem {H : Type} [Group H] [Fintype H] (z : MonoidAlgebra ℂ H) (hz : z * z = z) (g : H) :
    ∑ a, z.coeff a * z.coeff (a⁻¹ * g) = z.coeff g := by
  conv_rhs => rw [← hz]
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  simp

section Act

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G]

theorem mult_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) :
    Mult θ M J χ ≤ Mult θ M J' χ' :=
  Submodule.span_mono fun X hX => ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩

theorem postOn_gaL_mem (hθ : IsInfFam θ) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) {X : MMap M}
    (hX : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    postOn M (gaL V β L eG c) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
  have e : postOn M (gaL V β L eG c) X = ∑ g, c g • postOn M (actL V β L (eG g)) X := by
    ext v h
    simp [gaL, postOn_apply]
  rw [e]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _
    (GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity θ M hθ β L (eG g) X hX _ fun _ => rfl)

theorem gaL_gaL (hL : LiftsExist V β L) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g)
    {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) : gaL V β L eG c (gaL V β L eG c F) = gaL V β L eG c F := by
  letI : Fintype (G0 L.Pg L.r) := Fintype.ofEquiv G eG.toEquiv
  have e : ∀ F, gaL V β L eG c F = ∑ g, c (eG.symm g) • actG0 V β L g F := fun F => by
    unfold gaL
    rw [LinearMap.sum_apply]
    refine Fintype.sum_equiv eG.toEquiv _ _ fun g => ?_
    show c g • actG0 V β L (eG g) F = c (eG.symm (eG g)) • actG0 V β L (eG g) F
    rw [MulEquiv.symm_apply_apply]
  rw [e, e]
  refine GlobalTheory.FlagAction.convIdempotent_act V β L hL (fun g => c (eG.symm g)) (fun g => ?_) F hF
  rw [← hc]
  refine Fintype.sum_equiv eG.symm.toEquiv _ _ fun a => ?_
  show c (eG.symm a) * c (eG.symm (a⁻¹ * g)) = c (eG.symm a) * c ((eG.symm a)⁻¹ * eG.symm g)
  rw [map_mul, map_inv]

theorem postOn_gaL_mem_goodPart (hθ : IsInfFam θ) (hL : LiftsExist V β L) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)
    (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g) {X : MMap M}
    (hX : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    postOn M (gaL V β L eG c) X ∈
      goodPart θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) (gaL V β L eG c) := by
  refine ⟨postOn_gaL_mem hθ eG c hX, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  ext1 v
  exact gaL_gaL hL eG c hc (GlobalTheory.hasType_of_mem_mult θ M β _ X hX v)

end Act

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem liftsExist_rows (h : R.toLevCh.Is A.μ0) : LiftsExist (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  obtain ⟨c, hc⟩ := h.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  refine _root_.GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_) (Finset.disjoint_empty_right _)
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  obtain ⟨k', hk'⟩ := (h.Pg PP').1 (hP'.resolve_right (Finset.notMem_empty _))
  exact not_isConjPl R.C.P hk hk'

theorem eC_conv (hr : R.grp_record) (g : G) :
    ∑ a, RealDat.eC (A := A) D.what₂.embLL a * RealDat.eC (A := A) D.what₂.embLL (a⁻¹ * g) =
      RealDat.eC (A := A) D.what₂.embLL g := by
  obtain ⟨eR, _, _, h, _⟩ := hr
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G eR.toEquiv
  unfold RealDat.eC
  simp only [h]
  rw [← conv_of_idem _ (GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D).2 (eR g)]
  refine Fintype.sum_equiv eR.toEquiv _ _ fun a => ?_
  show _ = D.ntypes.e0.coeff (eR a) * D.ntypes.e0.coeff ((eR a)⁻¹ * eR g)
  rw [map_mul, map_inv]

theorem thDn_mem_CC (t : T) (x : (R.HX t).H) : R.thDn t x ∈ R.CC t 0 :=
  (Lift.thetaDn (R.CC t) (R.ioY t) (D.R.m - 1) (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict x))).2

theorem thDn_mem (t : T) (x : (R.HX t).H) :
    PiTensorProduct.lift.symm (R.thDn t x) ∈
      Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
  have hr : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Ranks.rankY]
  have e0 := GlobalTheory.levG_twist_trivial_of_rank_eq (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) hr R.Pg (R.Q t) R.triv
    R.chi (R.xiR t)
  have e1 := e0.1
  have e2 := e0.2
  have h1 : R.thDn t x ∈ MultT R.θ (R.MY 0) (levS _ (R.βY 0) (R.datYt t 0 R.triv)) (levChi _ (R.βY 0) (R.datYt t 0 R.triv)) :=
    thDn_mem_CC R t x
  have h2 := (mem_multT R.θ (R.MY 0) _ _ _).1 h1
  have e1' : levG (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = levG (Yc D 0) (R.βY 0) (R.dat0 R.triv) := e1
  have e2' : ∀ k ∈ levG (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv),
      levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) k = levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k := e2
  have h3 : ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 R.triv), k ∈ levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) ∧
      levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) k = levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k := fun k hk => by
    have hk' : k ∈ levG (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) := by rw [e1']; exact hk
    exact ⟨hk', e2' k hk'⟩
  exact mult_mono h3 h2

theorem proj_thDn_mem (h : R.toLevCh.Is A.μ0) (hθ : R.models_inf) (hr : R.grp_record) (t : T) (x : (R.HX t).H) :
    postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x)) ∈ R.EEat R.triv :=
  postOn_gaL_mem_goodPart (L := R.dat0 R.triv) hθ (liftsExist_rows R h) R.eG _ (eC_conv R hr) (thDn_mem R t x)

end Real

theorem exists_chain_Th : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → ∃ Th, ({ R with Th := Th } : RealDat D A Ks).chain_Th := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h _ hM hr
  have key : ∀ t, ∃ y : (R.HX t).H →ₗ[ℂ] R.HE.H,
      ∀ x, R.HE.e (y x) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x)) := fun t =>
    GlobalTheory.HilbertModel.exists_lift hM.HE
      (postOn (R.MY 0) R.e0 ∘ₗ
        (PiTensorProduct.lift.symm : (SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) ≃ₗ[ℂ] MMap (R.MY 0)).toLinearMap ∘ₗ R.thDn t)
      (proj_thDn_mem R h hM.inf hr t)
  choose Th hTh using key
  exact ⟨Th, hTh⟩

end GlobalTheory.ProjectedLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothPureTensorsSeparateTensorProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.PureSep

theorem exists_finite_subspaces {ι : Type} {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    (x : ⨂[ℂ] i, E i) : ∃ W : ∀ i, Submodule ℂ (E i), (∀ i, FiniteDimensional ℂ (W i)) ∧
      ∃ y : ⨂[ℂ] i, W i, PiTensorProduct.map (fun i => (W i).subtype) y = x := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    refine ⟨fun i => ℂ ∙ m i, fun i => inferInstance,
      r • PiTensorProduct.tprod ℂ (fun i => (⟨m i, Submodule.mem_span_singleton_self _⟩ : ℂ ∙ m i)), ?_⟩
    rw [map_smul, PiTensorProduct.map_tprod]
    rfl
  | add a b ha hb =>
    obtain ⟨W₁, h₁, y₁, rfl⟩ := ha
    obtain ⟨W₂, h₂, y₂, rfl⟩ := hb
    refine ⟨fun i => W₁ i ⊔ W₂ i, fun i => by have := h₁ i; have := h₂ i; infer_instance,
      PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_left : W₁ i ≤ W₁ i ⊔ W₂ i)) y₁ +
        PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_right : W₂ i ≤ W₁ i ⊔ W₂ i)) y₂, ?_⟩
    rw [map_add (f := _), ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
      ← PiTensorProduct.map_comp]
    rfl

theorem exists_ellT_ne_zero : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (x : SmT M), x ≠ 0 → ∃ w : M.Vec, ellT M (fun τ => (w τ : M.H τ)) (inclT M x) ≠ 0 := by
  classical
  intro D V S M x hx
  obtain ⟨W, hW, y, rfl⟩ := exists_finite_subspaces x
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (map_zero _)
  let ob : ∀ τ, OrthonormalBasis (Fin (Module.finrank ℂ (W τ))) ℂ (W τ) := fun τ =>
    haveI := hW τ; stdOrthonormalBasis ℂ (W τ)
  let B := Basis.piTensorProduct (fun τ => (ob τ).toBasis)
  obtain ⟨k, hk⟩ : ∃ k, B.repr y k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hy
    apply B.repr.injective (show B.repr y = B.repr 0 from ?_)
    ext k
    simp [h k]
  refine ⟨fun τ => ((ob τ (k τ) : W τ) : M.sm τ), ?_⟩
  have key : ∀ y' : ⨂[ℂ] τ, W τ,
      ellT M (fun τ => (((ob τ (k τ) : W τ) : M.sm τ) : M.H τ))
        (inclT M (PiTensorProduct.map (fun τ => (W τ).subtype) y')) = B.repr y' k := by
    intro y'
    induction y' using PiTensorProduct.induction_on with
    | smul_tprod r z =>
      unfold ellT inclT
      simp only [map_smul, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod, Finsupp.smul_apply, B,
        Basis.piTensorProduct_repr_tprod_apply, MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, innerₛₗ_apply_apply, smul_eq_mul]
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      rfl
    | add a b ha hb =>
      simp only [map_add (f := _), Finsupp.add_apply] at ha hb ⊢
      rw [ha, hb]
  exact fun h => hk ((key y).symm.trans h)

end GlobalTheory.Mem.PureSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedEvaluationSquareIntegrableNormAllRows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.EvalAllRows

theorem eq_zero_of_units {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (T : MMap M)
    (h : ∀ v : M.Vec, (∀ τ, ‖(v τ : M.H τ)‖ = 1) → T v = 0) : T = 0 := by
  classical
  refine MultilinearMap.ext fun v => ?_
  by_cases hz : ∃ τ, v τ = 0
  · obtain ⟨τ, hτ⟩ := hz
    exact T.map_coord_zero τ hτ
  · push_neg at hz
    have hn : ∀ τ, ‖(v τ : M.H τ)‖ ≠ 0 := fun τ e => hz τ (Subtype.ext (norm_eq_zero.1 e))
    let u : M.Vec := fun τ => ((‖(v τ : M.H τ)‖⁻¹ : ℝ) : ℂ) • v τ
    have hu : ∀ τ, ‖(u τ : M.H τ)‖ = 1 := fun τ => by
      simp only [u, Submodule.coe_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (hn τ)
    have hv : v = fun τ => ((‖(v τ : M.H τ)‖ : ℝ) : ℂ) • u τ := by
      funext τ
      simp only [u, smul_smul]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hn τ), Complex.ofReal_one, one_smul]
    rw [hv, T.map_smul_univ, h u hu, smul_zero]
    rfl

end GlobalTheory.EvalAllRows

theorem GlobalTheory.EvalAllRows.evalTranslate_norm_all : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ MultR R F, MemLp (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) 2 (muX X) ∧ ∫ x, ‖ev (MP R) v₀ S ((iotaX X h).symm x * t)‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  intro _ hCusp _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hHE hGap hL hinf hν0 hsee
  haveI hνH : R.ν0.IsHaarMeasure := hν0.1.1
  obtain ⟨c, hc, hmap⟩ := @GlobalTheory.EvalNormTransfer.exists_map_eq_smul D X h R.ν0 hνH
  obtain ⟨hι, hιs⟩ := measurable_of_borel X (iotaX X h) (GlobalTheory.EvalNormTransfer.borel_inst X)
  have hTr : SquareIntegrableTransfer R.ν0 R.fd0 X (iotaX X h).toMulEquiv t c :=
    squareIntegrableTransfer_of_rational_points R.ν0 R.fd0 X _ t c hι hιs hc hmap hνH hν0.2 (GlobalTheory.EvalNormTransfer.iotaX_rat X h)
  refine ⟨c, hc, fun v₀ hv S hS => ?_⟩
  have hSch : ∀ S' ∈ MultR R F, ∃ c', IsMultIP (MP R) R.ν0 R.fd0 S' S' c' := fun S' hS' =>
    GlobalTheory.MultFinite.schurMult hCusp R.ν0 R.fd0 hinf hνH hν0.2 S' hS' S' hS'
  have hcont : ∀ S' ∈ MultR R F, ∀ v, Continuous (S' v) ∧ ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S' v (γ * g) = S' v g :=
    fun S' hS' v => Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (M := R.MY 0) (θ := R.θ) (J := JR R F) (χ := chiR R F) hS' v
  haveI : BorelSpace (GA D (D.sp.Y 0)) := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (Yc D 0)
  have hL2 : ∀ S' ∈ MultR R F, ∀ v, MemLp (S' v) 2 (R.ν0.restrict R.fd0) := by
    intro S' hS' v
    obtain ⟨c', hip⟩ := hSch S' hS'
    refine (memLp_two_iff_integrable_sq_norm (hcont S' hS' v).1.measurable.aestronglyMeasurable).2
      (((hip v v).1).norm.congr (.of_forall fun x => ?_))
    simp only [norm_mul, norm_star, sq]
  obtain ⟨hm, hn⟩ := hTr (S v₀) (hcont S hS v₀).1 (hcont S hS v₀).2 (hL2 S hS v₀)
  refine ⟨hm, hn.trans (congrArg (c * ·) (re_ipM_eq (hSch S hS) hv).symm), ?_⟩
  intro h0
  refine GlobalTheory.EvalAllRows.eq_zero_of_units (MP R) S fun v hv' => ?_
  by_contra hne
  have hre := re_ipM_eq (hSch S hS) hv'
  have hint : IntegrableOn (fun x => ‖S v x‖ ^ 2) R.fd0 R.ν0 :=
    (memLp_two_iff_integrable_sq_norm (hL2 S hS v).aestronglyMeasurable).1 (hL2 S hS v)
  have hp := Formalism.IndefR.PeterssonHilbertSpace.petPos (D.sp.Y 0) R.ν0 R.fd0 hνH hν0.2 (S v) (hcont S hS v).1 (hcont S hS v).2 hne hint
  rw [← hre, h0] at hp
  exact lt_irrefl _ hp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XEUpdSZeroLam
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 2000000 in
theorem XE_updS_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) (hOk : A3.fam3.Ok3 1) (hsep : A3.fam3.TypesSep3)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) (b : Bool) :
    (((R.updS R.kap (zeroLam R F c)).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE := by
  have h := cx_XE_scal (R.toCx3 F) F.cr (zeroLam R F c) b fun p hp j v => by
    by_cases he : R.EEp3 p = ⊥
    · exact absurd (partPr_of_bot _ _ _ (qp_bot R F hC hP hOk hsep he b)) hp
    · exact zeroLam_of_ne R F c (hZ p he j).1 fun hv => (hZ p he j).2 v hv
  exact (by with_unfolding_all exact (h :))


set_option maxHeartbeats 2000000 in
def scalReadL (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3)
    (hX : ∀ b, (((R.updS R.kap lam).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) : ReadL (R.updS R.kap lam) F X0 Y :=
  { Z with
    met := fun v hv x y => (Z.met v hv x y).trans (by rw [hX true]; rfl)
    met0 := fun v hv x y => (Z.met0 v hv x y).trans (by rw [hX false]; rfl) }


end GlobalTheory.Mem.R3

end
end

