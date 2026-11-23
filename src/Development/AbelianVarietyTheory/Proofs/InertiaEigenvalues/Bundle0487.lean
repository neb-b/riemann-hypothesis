module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0460

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFixingKummerRootMovesLess
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.TameInertiaCyclic GlobalTheory.MemLoc.FrobLaws

noncomputable section
namespace GlobalTheory.NearRoot

variable {l : ℕ} [hl : Fact l.Prime]

theorem ratio_one (g : GQ l) : GlobalTheory.TameInertiaCyclic.ratio g 1 = 1 :=
  Subtype.ext (by show g 1 / 1 = 1; simp)

theorem ratio_pow (g : GQ l) (x : Om l) (n : ℕ) :
    GlobalTheory.TameInertiaCyclic.ratio g (x ^ n) = GlobalTheory.TameInertiaCyclic.ratio g x ^ n := by
  induction n with
  | zero => simpa using ratio_one g
  | succ n ih => rw [pow_succ, GlobalTheory.TameInertiaCyclic.ratio_mul, ih, pow_succ]

theorem norm_natCast_lt_one : ‖(l : Om l)‖ < 1 := by
  have h : ‖((l : ℚ_[l]) : Om l)‖ < 1 := by
    rw [PadicAlgCl.norm_extends]; exact Padic.norm_p_lt_one
  simpa using h

theorem natCast_ne_zero : (l : Om l) ≠ 0 := by
  have h : ((l : ℚ_[l]) : Om l) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] (Om l)).injective]
    exact_mod_cast hl.out.ne_zero
  simpa using h

theorem exists_unif (F : FinExt l) :
    ∃ ϖ ∈ F.1, ϖ ≠ 0 ∧ (∀ x ∈ F.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖ϖ ^ k‖) ∧
      ∃ E : ℕ, 0 < E ∧ ‖ϖ‖ ^ E = ‖(l : Om l)‖ := by
  obtain ⟨π, hπ, hπ0, hgen⟩ := GlobalTheory.TameInertiaCyclic.exists_gen F
  have hlF : (l : Om l) ∈ F.1 := natCast_mem _ l
  obtain ⟨k0, hk0⟩ := hgen _ hlF natCast_ne_zero
  have hk0' : k0 ≠ 0 := by
    rintro rfl
    have := norm_natCast_lt_one (l := l)
    rw [hk0] at this
    simp at this
  rcases lt_or_gt_of_ne hk0' with hneg | hpos
  · refine ⟨π⁻¹, inv_mem hπ, inv_ne_zero hπ0, fun x hx hx0 => ?_, (-k0).toNat, by omega, ?_⟩
    · obtain ⟨k, hk⟩ := hgen x hx hx0
      exact ⟨-k, by rw [hk, _root_.inv_zpow', neg_neg]⟩
    · rw [hk0, ← norm_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega), _root_.inv_zpow', neg_neg]
  · refine ⟨π, hπ, hπ0, hgen, k0.toNat, by omega, ?_⟩
    rw [hk0, ← norm_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]

theorem near_root : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧ ∀ ρ : Om l, ρ ^ M = -(l : Om l) → ∀ g : GQ l, (∀ y : Om l, ‖y‖ ≤ 1 → ‖g y - y‖ < 1) → g ρ = ρ → ∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖ := by
  intro l _ F
  obtain ⟨ϖ, hϖ, hϖ0, hgen, E, hE, hEn⟩ := exists_unif F
  obtain ⟨s, M, hlM, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hE.ne' l (Fact.out : l.Prime).ne_one
  have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hlM)
  refine ⟨M, hM, hlM, fun ρ hρ g hg hgρ x hx hx0 => ?_⟩
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne', eq_comm, neg_eq_zero] at hρ
    exact natCast_ne_zero hρ
  have hq0 : ϖ ^ (l ^ s) ≠ 0 := pow_ne_zero _ hϖ0
  have hnq : ‖ϖ ^ (l ^ s)‖ = ‖ρ‖ := by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hM.ne').1 ?_
    rw [← norm_pow, ← pow_mul, norm_pow, hEn, ← norm_pow, hρ, norm_neg]
  set u := ϖ ^ (l ^ s) / ρ with hu
  have hu0 : u ≠ 0 := div_ne_zero hq0 hρ0
  have hnu : ‖u‖ = 1 := by rw [hu, norm_div, hnq, div_self (norm_ne_zero_iff.2 hρ0)]
  have h1 : res (GlobalTheory.TameInertiaCyclic.ratio g u) = 1 := by
    rw [GlobalTheory.TameInertiaCyclic.res_ratio_iff g hu0, hnu]; exact hg u hnu.le
  have h2 : res (GlobalTheory.TameInertiaCyclic.ratio g ρ) = 1 := by
    rw [GlobalTheory.TameInertiaCyclic.res_ratio_iff g hρ0, hgρ, sub_self, norm_zero]
    exact norm_pos_iff.2 hρ0
  have h3 : res (GlobalTheory.TameInertiaCyclic.ratio g ϖ) ^ (l ^ s) = 1 := by
    rw [← map_pow, ← ratio_pow, ← div_mul_cancel₀ (ϖ ^ (l ^ s)) hρ0, ← hu,
      GlobalTheory.TameInertiaCyclic.ratio_mul, map_mul, h1, h2, one_mul]
  have h4 : res (GlobalTheory.TameInertiaCyclic.ratio g ϖ) = 1 := by
    have h5 : (res (GlobalTheory.TameInertiaCyclic.ratio g ϖ) - 1) ^ (l ^ s) = 0 := by
      rw [sub_pow_char_pow, h3, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 h5)
  obtain ⟨k, hk⟩ := hgen x hx hx0
  have hp : ϖ ^ k ≠ 0 := zpow_ne_zero k hϖ0
  have hv : ‖x / ϖ ^ k‖ = 1 := by rw [norm_div, hk, div_self (norm_ne_zero_iff.2 hp)]
  have h6 : res (GlobalTheory.TameInertiaCyclic.ratio g (x / ϖ ^ k)) = 1 := by
    rw [GlobalTheory.TameInertiaCyclic.res_ratio_iff _ (div_ne_zero hx0 hp), hv]
    exact hg _ hv.le
  rw [← GlobalTheory.TameInertiaCyclic.res_ratio_iff _ hx0, ← div_mul_cancel₀ x hp,
    GlobalTheory.TameInertiaCyclic.ratio_mul, map_mul, h6,
    GlobalTheory.TameInertiaCyclic.res_ratio_zpow _ hϖ0 h4, one_mul]

end GlobalTheory.NearRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughCharactersLatticeCoefficientExtens
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

noncomputable section

namespace GlobalTheory.BaseCoefIner

section Ext

variable {K L : Type} [Field K] [Field L] [Algebra K L] {W : Type} [AddCommGroup W] [Module K W]

theorem extS_mono {S T : Submodule K W} (h : S ≤ T) : CJ.extS L S ≤ CJ.extS L T := by
  have := CJ.extS_inf (L := L) S T
  rw [inf_eq_left.2 h] at this
  rw [this]
  exact inf_le_right

theorem extS_iSup_le {J : Sort*} (S : J → Submodule K W) :
    CJ.extS L (⨆ j, S j) ≤ ⨆ j, CJ.extS L (S j) := by
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | tmul c s =>
    obtain ⟨s, hs⟩ := s
    rw [LinearMap.baseChange_tmul]
    change c ⊗ₜ[K] s ∈ _
    induction hs using Submodule.iSup_induction' with
    | mem j x hx =>
      exact Submodule.mem_iSup_of_mem j ⟨c ⊗ₜ[K] (⟨x, hx⟩ : S j), by simp [LinearMap.baseChange_tmul]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [tmul_add]; exact Submodule.add_mem _ hx hy

end Ext

section Main

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL']

section Tower

variable [Algebra LL LL'] [IsScalarTower Qp LL LL'] {k : ℕ}

theorem comm_act_smul (A : Matrix (Fin k) (Fin k) LL) (β : B →ₗ[Qp] B) (r : LL)
    (x : LL' ⊗[LL] ((Fin k → LL) ⊗[Qp] B)) :
    CJ.EE (Qp := Qp) (LL' := LL') B ((PI.CoefExt.actT A β - r • LinearMap.id).baseChange LL' x)
      = (PI.CoefExt.actT (A.map (algebraMap LL LL')) β - (algebraMap LL LL' r) • LinearMap.id :
        (Fin k → LL') ⊗[Qp] B →ₗ[LL'] (Fin k → LL') ⊗[Qp] B) (CJ.EE B x) := by
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.sub_apply, map_sub,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.id_apply, ← algebraMap_smul LL' r x, map_smul]
  congr 1
  exact PI.CoefExt.coefEquiv_comm A β x

theorem dpcris_ext (M : G →* Matrix (Fin k) (Fin k) LL) :
    (CJ.extS LL' (PC.Dpcris (CJ.rep M))).map ((CJ.EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) B :
        _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _)
      = PC.Dpcris (CJ.rep (((IsScalarTower.toAlgHom Qp LL LL').mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M)) := by
  unfold PotCrysData.Dpcris Dcris
  rw [CJ.extS_iInf]
  simp only [CJ.extS_ker]
  exact CJ.map_iInf_ker _ _ _ (fun g x => CJ.comm_act (BdR := B) (M g) _ x)

theorem eig_ext (M : G →* Matrix (Fin k) (Fin k) LL) (I : Subgroup G) (a : I →* LLˣ) :
    (CJ.extS LL' (PC.Eig (CJ.rep M) I a)).map ((CJ.EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) B :
        _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _)
      = PC.Eig (CJ.rep (((IsScalarTower.toAlgHom Qp LL LL').mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M)) I
          ((Units.map (algebraMap LL LL' : LL →* LL')).comp a) := by
  unfold PotCrysData.Eig
  rw [CJ.extS_inf, CJ.map_inf_equiv, dpcris_ext, CJ.extS_iInf]
  simp only [CJ.extS_ker]
  congr 1
  exact CJ.map_iInf_ker _ _ _ (fun g x => comm_act_smul (M g) _ _ x)

end Tower

theorem orderOf_comp {I : Type} [Group I] (f : LL →+* LL') (a : I →* LLˣ) :
    orderOf ((Units.map (f : LL →* LL')).comp a) = orderOf a := by
  refine orderOf_eq_orderOf_iff.2 fun n => ?_
  simp only [MonoidHom.ext_iff, MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.one_apply]
  refine forall_congr' fun g => ?_
  rw [← map_pow]
  exact map_eq_one_iff _ (Units.map_injective f.injective)

theorem inertiaThrough_mat (f : LL →ₐ[Qp] LL') {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL)
    (Sig : Finset (PC.Iner →* LLˣ)) (hS : PC.InertiaThrough (CJ.rep M) Sig) :
    PC.InertiaThrough (CJ.rep ((f.mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M))
      (mapSig f.toRingHom Sig) := by
  classical
  let _ : Algebra LL LL' := f.toRingHom.toAlgebra
  have _ : IsScalarTower Qp LL LL' := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  have hf : IsScalarTower.toAlgHom Qp LL LL' = f := AlgHom.ext fun _ => rfl
  have hm : ∀ c, c ∈ mapSig f.toRingHom Sig ↔
      ∃ a ∈ Sig, (Units.map (f.toRingHom : LL →* LL')).comp a = c := fun c => by
    unfold mapSig
    convert Finset.mem_image
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨fun c hc g hg => ?_, fun c hc => ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (hm c).1 hc
    rw [MonoidHom.comp_apply, h1 a ha g hg, map_one]
  · obtain ⟨a, ha, rfl⟩ := (hm c).1 hc
    rw [orderOf_comp]
    exact h2 a ha
  · have hD := dpcris_ext (LL' := LL') PC M
    rw [hf] at hD
    refine hD.symm.le.trans (Submodule.map_le_iff_le_comap.2 ?_)
    refine (extS_mono h3.le).trans ?_
    refine (extS_iSup_le _).trans (iSup_le fun a => (extS_iSup_le _).trans (iSup_le fun ha => ?_))
    refine Submodule.map_le_iff_le_comap.1 ?_
    have hE := eig_ext (LL' := LL') PC M PC.Iner a
    rw [hf] at hE
    refine hE.le.trans ?_
    exact le_iSup₂_of_le ((Units.map (f.toRingHom : LL →* LL')).comp a) ((hm _).2 ⟨a, ha, rfl⟩) le_rfl
  · exact iSup₂_le fun _ _ => inf_le_left

theorem inertiaThrough_basis (f : LL →ₐ[Qp] LL') {k : ℕ}
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (b : Module.Basis (Fin k) LL V)
    (Sig : Finset (PC.Iner →* LLˣ)) (hS : PC.InertiaThrough ρ Sig) :
    PC.InertiaThrough (CJ.rep ((f.mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp
          ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ)))
      (mapSig f.toRingHom Sig) := by
  refine inertiaThrough_mat _ f _ Sig ?_
  refine (GlobalTheory.HTW.Rec.potCrys_inertiaThrough_of_equiv _ b.equivFun.symm ?_).2 Sig hS
  intro g v
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  change (LinearMap.toMatrix b b (ρ g)).mulVec v = _
  have := LinearMap.toMatrix_mulVec_repr b b (ρ g) (b.equivFun.symm v)
  rw [← Module.Basis.equivFun_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] at this
  exact this

end Main


set_option maxHeartbeats 1000000 in
theorem main : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (Sig : Finset ((pc Pl h hN hF hS).Iner →* (↥LL.1)ˣ)), (pc Pl h hN hF hS).InertiaThrough T.ρ Sig → (pc Pl h hN hF hS).InertiaThrough (extLat hL T b hb).ρ (mapSig (incl hL).toRingHom Sig) := by
  intro l _ Pl K' h hN hF hS LL LL' hL T k b hb Sig hI
  exact inertiaThrough_basis (pc Pl h hN hF hS) (incl hL) T.ρ b Sig hI

end GlobalTheory.BaseCoefIner
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjOnCharValuesAndLengthQuotient
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.CharValueLength

variable {l : ℕ} [Fact l.Prime] in
private theorem isUnit_of_toZMod_ne_zero' {x : ℤ_[l]} (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact hx

variable {l : ℕ} [Fact l.Prime] in
private theorem principalUnit_pow_prime_eq_one_add_pow_succ {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r)
    (h2 : l = 2 → 2 ≤ r) (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ l = 1 + (l : ℤ_[l]) ^ (r + 1) * w' := by
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨n, hn⟩ : ∃ n, l = n + 2 := ⟨l - 2, by omega⟩
  set x := (l : ℤ_[l]) ^ r * w with hx
  have hexp : u ^ l = (∑ j ∈ Finset.range (n + 1),
      x ^ (j + 1 + 1) * ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l])) + x * l + 1 := by
    rw [hu, add_comm, add_pow, show l + 1 = n + 1 + 1 + 1 by omega, Finset.sum_range_succ',
      Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, pow_one, Nat.choose_zero_right, Nat.choose_one_right,
      Nat.cast_one, zero_add]
  have hdvd : (l : ℤ_[l]) ^ (r + 2) ∣ ∑ j ∈ Finset.range (n + 1),
      x ^ (j + 1 + 1) * ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l]) := by
    refine Finset.dvd_sum fun j hj => ?_
    have hj' : j + 2 ≤ l := by rw [Finset.mem_range] at hj; omega
    have hxp : x ^ (j + 1 + 1) = (l : ℤ_[l]) ^ (r * (j + 1 + 1)) * w ^ (j + 1 + 1) := by
      rw [hx, mul_pow, ← pow_mul]
    rcases Nat.lt_or_ge (j + 2) l with hlt | hge
    · have hc : (l : ℤ_[l]) ∣ ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l]) :=
        Nat.cast_dvd_cast ((Fact.out : l.Prime).dvd_choose_self (by omega) (by omega))
      have h1 : (l : ℤ_[l]) ^ (r + 2) ∣ (l : ℤ_[l]) ^ (r * (j + 1 + 1)) * l := by
        rw [← pow_succ]; exact pow_dvd_pow _ (by nlinarith)
      exact h1.trans (mul_dvd_mul (Dvd.intro _ hxp.symm) hc)
    · have hle : r + 2 ≤ r * (j + 1 + 1) := by
        rcases Nat.lt_or_ge l 3 with h | h
        · have := h2 (by omega); nlinarith
        · nlinarith
      exact ((pow_dvd_pow _ hle).trans (Dvd.intro _ hxp.symm)).mul_right _
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨w + l * c, isUnit_of_toZMod_ne_zero' ?_, ?_⟩
  · simpa [ZMod.natCast_self] using (hw.map PadicInt.toZMod).ne_zero
  · rw [hexp, hc, hx]; ring

variable {l : ℕ} [Fact l.Prime] in
private theorem toZMod_principalUnit_eq_one {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r)
    (hu : u = 1 + (l : ℤ_[l]) ^ r * w) : PadicInt.toZMod u = 1 := by
  rw [hu]
  simp [ZMod.natCast_self, zero_pow (Nat.one_le_iff_ne_zero.1 hr)]

variable {l : ℕ} [Fact l.Prime] in
private theorem principalUnit_pow_of_not_dvd {u w : ℤ_[l]} {r m : ℕ} (hr : 1 ≤ r)
    (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) (hm : ¬ l ∣ m) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ m = 1 + (l : ℤ_[l]) ^ r * w' := by
  refine ⟨w * ∑ i ∈ Finset.range m, u ^ i, hw.mul (isUnit_of_toZMod_ne_zero' ?_), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
  · rw [map_sum]
    simp only [map_pow, toZMod_principalUnit_eq_one hr hu, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    exact fun h => hm ((ZMod.natCast_eq_zero_iff m l).1 h)
  · have hg := geom_sum_mul u m
    have hu1 : u - 1 = (l : ℤ_[l]) ^ r * w := by rw [hu]; ring
    rw [hu1] at hg
    linear_combination -hg

variable {l : ℕ} [Fact l.Prime] in
private theorem principalUnit_pow_eq_one_add_pow_add_padicValNat {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r) (h2 : l = 2 → 2 ≤ r)
    (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) {k : ℕ} (hk : k ≠ 0) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ k = 1 + (l : ℤ_[l]) ^ (r + padicValNat l k) * w' := by
  have hpow : ∀ a : ℕ, ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ (l ^ a) = 1 + (l : ℤ_[l]) ^ (r + a) * w' := by
    intro a
    induction a with
    | zero => exact ⟨w, hw, by simpa using hu⟩
    | succ a ih =>
      obtain ⟨w', hw', h'⟩ := ih
      obtain ⟨w'', hw'', h''⟩ :=
        principalUnit_pow_prime_eq_one_add_pow_succ (by omega) (fun h => by have := h2 h; omega) hw' h'
      exact ⟨w'', hw'', by rw [pow_succ, pow_mul, h'', ← add_assoc]⟩
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk l (Fact.out : l.Prime).one_lt.ne'
  obtain ⟨w', hw', h'⟩ := hpow a
  obtain ⟨w'', hw'', h''⟩ := principalUnit_pow_of_not_dvd (by omega) hw' h' hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero l)
  refine ⟨w'', hw'', ?_⟩
  rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) hm0,
    Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero, pow_mul, h'']

private theorem length_quotient_span_unit_mul_pow_eq {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) (w : Oˣ) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {(w : O) * ϖ ^ n}) = n := by
  rw [Ideal.span_singleton_mul_left_unit w.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O n

theorem _root_.GlobalTheory.CharValueLength.injOn_and_lenUnit : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [CharZero O] (s t : ℕ) (u v : ℤ_[l]ˣ) (χ : ℕ → Oˣ), 1 ≤ s → (l = 2 → 2 ≤ s) → (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s * (v : ℤ_[l]) → (∀ c : ℕ, 1 ≤ c → c ≤ t → χ c = χ 1 * (Units.map (algebraMap ℤ_[l] O).toMonoidHom u) ^ (-((c : ℤ) - 1))) → Set.InjOn (fun c => (χ c : O)) (Finset.Icc 1 t : Set ℕ) ∧ _root_.Formalism.BasicNotions.lenUnit (O := O) l (O ⧸ Ideal.span {∏ c ∈ Finset.Ioc 1 t, ((χ 1 : O) - (χ c : O))}) = ∑ k ∈ Finset.Ioo 0 t, ((s : ℚ) + padicValNat l k) := by
  intro l _ O _ _ _ _ _ _ s t u v χ hs hs2 huv hχ
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hD : ∀ k : ℕ, k ≠ 0 → ∃ ε : Oˣ,
      algebraMap ℤ_[l] O u ^ k - 1 = ε * (l : O) ^ (s + padicValNat l k) := by
    intro k hk
    obtain ⟨w', hw', h'⟩ := principalUnit_pow_eq_one_add_pow_add_padicValNat hs hs2 v.isUnit huv hk
    refine ⟨(hw'.map (algebraMap ℤ_[l] O)).unit, ?_⟩
    rw [IsUnit.unit_spec, ← map_pow, h', map_add (f := _), map_one, map_mul, map_pow, map_natCast]
    ring
  have hrel : ∀ c, 1 ≤ c → c ≤ t → (χ c : O) * algebraMap ℤ_[l] O u ^ (c - 1) = χ 1 := by
    intro c h1 h2
    have h : χ c * (Units.map (algebraMap ℤ_[l] O).toMonoidHom u) ^ (c - 1) = χ 1 := by
      rw [hχ c h1 h2, mul_assoc, ← zpow_natCast, ← zpow_add, Nat.cast_sub h1, Nat.cast_one,
        neg_add_cancel, zpow_zero, mul_one]
    have h' := congrArg (fun z : Oˣ => (z : O)) h
    simpa using h'
  have hφu : IsUnit (algebraMap ℤ_[l] O u) := u.isUnit.map _
  constructor
  · intro c hc c' hc' heq
    simp only [Finset.coe_Icc, Set.mem_Icc] at hc hc'
    simp only at heq
    have key : ∀ a b : ℕ, 1 ≤ a ∧ a ≤ t → 1 ≤ b ∧ b ≤ t → (χ a : O) = χ b → a ≤ b → a = b := by
      intro c c' hc hc' heq hle
      by_contra hne
      obtain ⟨ε, hε⟩ := hD (c' - c) (by omega)
      have e1 := hrel c hc.1 hc.2
      have e2 := hrel c' hc'.1 hc'.2
      rw [← heq, show c' - 1 = (c - 1) + (c' - c) by omega, pow_add] at e2
      have h0 : (χ c : O) * algebraMap ℤ_[l] O u ^ (c - 1) *
          (algebraMap ℤ_[l] O u ^ (c' - c) - 1) = 0 := by
        linear_combination e2 - e1
      rcases mul_eq_zero.1 h0 with h | h
      · exact ((χ c).isUnit.mul (hφu.pow _)).ne_zero h
      · rw [hε] at h
        exact mul_ne_zero ε.ne_zero (pow_ne_zero _ hl0) h
    rcases le_total c c' with hle | hle
    · exact key c c' hc hc' heq hle
    · exact (key c' c hc' hc heq.symm hle).symm
  · have hterm : ∀ c ∈ Finset.Ioc 1 t, ∃ ε : Oˣ,
        (χ 1 : O) - χ c = ε * (l : O) ^ (s + padicValNat l (c - 1)) := by
      intro c hc
      rw [Finset.mem_Ioc] at hc
      obtain ⟨ε, hε⟩ := hD (c - 1) (by omega)
      refine ⟨χ c * ε, ?_⟩
      rw [← hrel c (by omega) hc.2, Units.val_mul, mul_assoc, ← hε]
      ring
    choose! ε hε using hterm
    have hprod : ∏ c ∈ Finset.Ioc 1 t, ((χ 1 : O) - χ c) =
        ((∏ c ∈ Finset.Ioc 1 t, ε c : Oˣ) : O) *
          (l : O) ^ (∑ c ∈ Finset.Ioc 1 t, (s + padicValNat l (c - 1))) := by
      rw [Finset.prod_congr rfl hε, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        Units.coe_prod]
    have hsum : ∑ c ∈ Finset.Ioc 1 t, (s + padicValNat l (c - 1)) =
        ∑ k ∈ Finset.Ioo 0 t, (s + padicValNat l k) := by
      refine Finset.sum_nbij' (fun c => c - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_ <;> intro a ha <;>
        simp only [Finset.mem_Ioc, Finset.mem_Ioo] at ha ⊢ <;> omega
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨e, η, hη⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
    have he : e ≠ 0 := by
      rintro rfl
      have hm : (Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O)).IsMaximal :=
        Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) (IsLocalRing.maximalIdeal O)
      have hl : (l : ℤ_[l]) ∈ Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O) := by
        rw [IsLocalRing.eq_maximalIdeal hm, PadicInt.maximalIdeal_eq_span_p]
        exact Ideal.subset_span rfl
      rw [Ideal.mem_comap, map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hl
      exact hl (by rw [hη, pow_zero, mul_one]; exact η.isUnit)
    unfold _root_.Formalism.BasicNotions.lenUnit
    rw [hprod, hsum, hη, mul_pow, ← pow_mul, ← mul_assoc, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, length_quotient_span_unit_mul_pow_eq hϖ, length_quotient_span_unit_mul_pow_eq hϖ,
      ENat.toNat_natCast, ENat.toNat_natCast, Nat.cast_mul,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 he)]
    push_cast
    rfl

end GlobalTheory.CharValueLength
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodLatticeKernelOfSurjectionGoodLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGoodLattice_kernel_of_surjection_goodLattice : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → ∃ (T₀ : QLat LL) (f : LatHom T₀.L T₁.L), IsSESLat (Qp := ℚ_[l]) f g ∧ IsGood a ϖ Pl T₀ Sig U := by
  first | exact @GlobalTheory.KerGood.main | exact GlobalTheory.KerGood.main | (intros; apply GlobalTheory.KerGood.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHodgeTateJumpOfGaloisFixedFiltrationVectorStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHodgeTateJump_of_galois_fixed_filtration_vector : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (LL : FinExt l) (T : QLat LL) (F : FinExt l), IsGalois ℚ_[l] ↥F.1 → ∀ (i : ℤ) (x : T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ g : Gl l, (g : GQ l) ∈ GK F → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) → x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i → x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) → ∀ τ, IsJumpV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ i := by
  first | exact @GlobalTheory.BKGal.isJumpV_of_fixed | exact GlobalTheory.BKGal.isJumpV_of_fixed | (intros; apply GlobalTheory.BKGal.isJumpV_of_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOtherRootFactorsActionFirstCoordinateStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_other_root_factors_action_first_coordinate : ∀ {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ} (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))) (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O), 2 ≤ t → (∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2)) → (∀ u, e ((X₀.map (toFr O)).mulVec u) = (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c)) → ∀ u, e (((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) = (0, fun c : Fin t => if (c : ℕ) = 0 then toFr O (∏ c' ∈ Finset.Ioc 1 t, (ρ 1 - ρ c')) * (e u).2 c else 0) := by
  first | exact @GlobalTheory.RootFactorProduct.prod_other_factors_action | exact GlobalTheory.RootFactorProduct.prod_other_factors_action | (intros; apply GlobalTheory.RootFactorProduct.prod_other_factors_action <;> assumption)
end

