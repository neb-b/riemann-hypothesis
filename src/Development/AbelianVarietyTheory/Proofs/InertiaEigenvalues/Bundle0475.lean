module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EPowXiExtMemMan
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
variable {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem YD_xiExt (P : PhiMod O K l e a ι) (α : ℕ)
    (hb : ∀ d : P.D, E K l e ^ α • P.xi d ∈ P.Man) {w : Vec K a ι} (hw : w ∈ P.Mext (invL l (S O K e))) :
    YD t ϖ (E K l e ^ α • P.xiExt w) = ∑ k, ϖ.iD t K (fun τ => hatR O (w τ k)) •
      YD t ϖ (E K l e ^ α • P.xi (fun _ => Pi.single k 1)) := by
  funext i
  simp only [YD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  congr 1
  funext τ
  have hw' : ∀ k, w τ k ∈ Rpi O K l e := fun k => invL_S_le_Rpi l e (mem_tot.1 hw τ k)
  have hb' : ∀ k, E K l e ^ α * P.xi (fun _ => Pi.single k 1) τ i ∈ Rpi O K l e := fun k =>
    mem_Rpi_of_mem_Man (hb (fun _ => Pi.single k 1)) τ i
  have hx : ∀ k, P.xi (fun _ => Pi.single k 1) τ i = P.xiMat τ i k := fun k => by
    rw [P.xi_apply, P.xiExt_apply]
    have : (cst (fun _ => Pi.single k 1 : P.D) : Vec K a ι) τ = Pi.single k 1 := by
      funext j
      change C ((Pi.single k 1 : ι → K) j) = _
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [this]
    simp
  have hs : E K l e ^ α * P.xiExt w τ i = ∑ k, w τ k * (E K l e ^ α * P.xi (fun _ => Pi.single k 1) τ i) := by
    simp only [hx, P.xiExt_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hm : (∑ k, w τ k * (E K l e ^ α * P.xi (fun _ => Pi.single k 1) τ i)) ∈ Rpi O K l e :=
    Subalgebra.sum_mem _ fun k _ => mul_mem (hw' k) (hb' k)
  rw [hs, hatR_of_mem (O := O) hm, Finset.sum_apply]
  simp only [Pi.mul_apply, hatR_of_mem (O := O) (hw' _), hatR_of_mem (O := O) (hb' _), ← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  congr 1
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  rfl


omit [NeZero a] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem cst_mem_Mext (P : PhiMod O K l e a ι) (d : P.D) : (cst d : Vec K a ι) ∈ P.Mext (invL l (S O K e)) := by
  refine mem_tot.2 fun τ i => ?_
  exact HasK.C_mem (d τ i)


omit [NeZero a] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem descN_mem_Mext (P : PhiMod O K l e a ι) (i : ℕ) (w : Vec K a ι) (hw : w ∈ P.Mext (invL l (S O K e))) :
    (fun τ j => descN K i (w τ j)) ∈ P.Mext (invL l (S O K e)) := by
  refine mem_tot.2 fun τ j => ?_
  obtain ⟨n, hn⟩ := mem_tot.1 hw τ j
  refine ⟨n, ?_⟩
  have h3 : (((l : S O K e) : K⟦X⟧)) ^ n = C ((l : K) ^ n) := by simp
  have h := descN_mem_S e i hn
  rwa [h3, ← smul_eq_C_mul, map_smul, smul_eq_C_mul, ← h3] at h

theorem E_pow_xiExt_mem_Man (P : PhiMod O K l e a ι) (α : ℕ) (hα : ∀ v ∈ P.L, E K l e ^ α • v ∈ P.M)
    (w : Vec K a ι) (hw : w ∈ P.Mext (invL l (S O K e))) : E K l e ^ α • P.xiExt w ∈ P.Man := by
  have h1 : P.xiExt w ∈ P.MMl := ((GlobalTheory.BK.xi_trivialises_invL_S O K l e a ι P).2 w).2 hw
  refine P.mem_Man.2 (mem_tot.2 fun τ i => ?_)
  obtain ⟨m, hm, h⟩ := P.mem_extc.1 (mem_tot.1 h1 τ)
  have hc : ∀ k, E K l e ^ α * P.mx τ i k ∈ A O K := fun k => by
    have hv : (Pi.single τ ((P.mx τ).col k) : Vec K a ι) ∈ P.L := mem_tot.2 fun σ => by
      by_cases hσ : σ = τ
      · subst hσ
        rw [Pi.single_eq_same]
        exact Submodule.subset_span ⟨k, rfl⟩
      · rw [Pi.single_eq_of_ne hσ]
        exact zero_mem _
    have h2 := mem_tot.1 (hα _ hv) τ i
    rwa [Pi.smul_apply, Pi.single_eq_same] at h2
  rw [Pi.smul_apply, h, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Subalgebra.sum_mem _ fun k _ => ?_
  rw [← mul_assoc]
  exact mul_mem (invL_S_le_Rpi l e (le_away _ _ (A_le_S l e (hc k)))) (invL_S_le_Rpi l e (hm k))

theorem taylor_vec (P : PhiMod O K l e a ι) (α : ℕ)
    (hdesc : ∀ (i : ℕ) (w : Vec K a ι), w ∈ P.Mext (invL l (S O K e)) →
      (fun τ j => descN K i (w τ j)) ∈ P.Mext (invL l (S O K e)))
    (hman : ∀ w ∈ P.Mext (invL l (S O K e)), E K l e ^ α • P.xiExt w ∈ P.Man)
    (σ : OD l O → OD l O) (ρ : (ι → OD l O) →+ (ι → OD l O)) (hρ : ∀ c y, ρ (c • y) = σ c • ρ y) (c : OD l O)
    (hor : ∀ d : P.D, ρ (YD t ϖ (E K l e ^ α • P.xi d)) = c • YD t ϖ (E K l e ^ α • P.xi d))
    (μ : ℕ → OD l O) (R : ℕ) (J : Ideal (OD l O))
    (hscal : ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ invL l (S O K e)) → σ (ϖ.iD t K (fun τ => hatR O (f τ))) -
      ∑ i ∈ Finset.range R, μ i * ϖ.iD t K (fun τ => hatR O (descN K i (f τ))) ∈ J)
    {w : Vec K a ι} (hw : w ∈ P.Mext (invL l (S O K e))) (j : ι) :
    ρ (YD t ϖ (E K l e ^ α • P.xiExt w)) j - c * ∑ i ∈ Finset.range R, μ i *
      YD t ϖ (E K l e ^ α • P.xiExt (fun τ k => descN K i (w τ k))) j ∈ J := by
  have hb : ∀ d : P.D, E K l e ^ α • P.xi d ∈ P.Man := fun d => hman _ (cst_mem_Mext P d)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [YD_xiExt t ϖ P α hb hw, map_sum]
  simp only [YD_xiExt t ϖ P α hb (hdesc _ w hw), hρ, hor, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine J.sum_mem fun k _ => ?_
  have h := J.mul_mem_left (c * YD t ϖ (E K l e ^ α • P.xi (fun _ => Pi.single k 1)) j)
    (hscal (fun τ => w τ k) fun τ => mem_tot.1 hw τ k)
  convert h using 1
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
def rhoDHom {LL : FinExt l} {ι : Type} (T : QLat LL)
    (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (g : Gl l) :
    (ι → OD l ↥(OL LL)) →+ (ι → OD l ↥(OL LL)) :=
  AddMonoidHom.mk' (rhoD T jD g) fun x y => by
    have h1 : jD (x + y) = jD x + jD y := jD.map_add x y
    have h2 := (TWact (galOD ↥(OL LL) (sQ l g)) T g).map_add (jD x) (jD y)
    have h3 := jD.symm.map_add (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD x)) (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD y))
    exact (congrArg (fun z => jD.symm (TWact (galOD ↥(OL LL) (sQ l g)) T g z)) h1).trans
      ((congrArg jD.symm h2).trans h3)
end GlobalTheory.GalStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMulBijectiveShiftsFiltrationV
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.PiSys

theorem iD_const_Ehat_eq_tmul (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) :
    ϖ.iD t K (fun _ => Ehat O K l e) = (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
  rw [iD, glue_const, Ehat, iHat_ofAl]
  exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))

end GlobalTheory.BKReal.PiSys

namespace GlobalTheory.BKReal.EhatShift

variable {l : ℕ} [Fact l.Prime]

theorem ev_eis_assoc_xi {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {ε : Per.Fl l} (hE : GlobalTheory.MemLoc.IsEps ε) :
    (∃ c : Per.Ainf l, c * GlobalTheory.MemLoc.xi ε = ϖ.ev a (eis l a e)) ∧
      ∃ c' : Per.Ainf l, c' * ϖ.ev a (eis l a e) = GlobalTheory.MemLoc.xi ε := by
  have hsp := (ϖ.span_ev_eis a).trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  refine ⟨Ideal.mem_span_singleton'.1 ?_, Ideal.mem_span_singleton'.1 ?_⟩
  · rw [← hsp]; exact Ideal.mem_span_singleton_self _
  · rw [hsp]; exact Ideal.mem_span_singleton_self _

theorem isUnit_and_mem_FilD_iff {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) :
    IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)))) ∧
      ∀ (j : ℤ) (x : Per.BdR l), x ∈ Per.FilD l j ↔
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) * x ∈ Per.FilD l (j + 1) := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ := ev_eis_assoc_xi (a := a) ϖ hE
  set U := (GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE).unit with hUdef
  have hU : (U : Per.BdR l) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi ε)) :=
    IsUnit.unit_spec _
  have hα : algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c) * (U : Per.BdR l) := by
    rw [hU, ← map_mul, ← map_mul, hc]
  have hβ : algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') *
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) = (U : Per.BdR l) := by
    rw [hU, ← map_mul, ← map_mul, hc']
  refine ⟨IsUnit.of_mul_eq_one
    (algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') * ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l)) ?_, ?_⟩
  · rw [← mul_assoc, mul_comm _ (algebraMap _ _ (GlobalTheory.MemLoc.aDp l c')), hβ, Units.mul_inv]
  intro j x
  rw [GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff hE, GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff hE, ← hUdef]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨GlobalTheory.MemLoc.aDp l c * w, ?_⟩
    rw [hα, _root_.zpow_add_one, Units.val_mul, map_mul]
    ring
  · rintro ⟨w, hw⟩
    refine ⟨GlobalTheory.MemLoc.aDp l c' * w, ?_⟩
    have h2 : (U : Per.BdR l) * x = (U : Per.BdR l) * (((U ^ j : (Per.BdR l)ˣ) : Per.BdR l) *
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c' * w)) := by
      calc (U : Per.BdR l) * x = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') *
            (algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) * x) := by
              rw [← mul_assoc, hβ]
        _ = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') *
            (((U ^ (j + 1) : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w) := by rw [hw]
        _ = _ := by rw [_root_.zpow_add_one, Units.val_mul, map_mul]; ring
    exact U.isUnit.mul_left_cancel h2

variable {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)

theorem isUnit_and_mem_Fil_iff {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (K : FinExt l) :
    IsUnit (GlobalTheory.BKGal.JumpDR.cD Td (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)))) ∧
      ∀ (j : ℤ) (x : Pl.R.BdR), x ∈ (Pl.PD K).Fil j ↔
        GlobalTheory.BKGal.JumpDR.cD Td (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) * x ∈ (Pl.PD K).Fil (j + 1) := by
  obtain ⟨hu, hF⟩ := isUnit_and_mem_FilD_iff (l := l) (a := a) ϖ
  have hc : Td.eD (GlobalTheory.BKGal.JumpDR.cD Td (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) :=
    RingEquiv.apply_symm_apply _ _
  refine ⟨?_, fun j x => ?_⟩
  · have := hu.map (Td.eD.symm : Per.BdR l →+* Pl.R.BdR)
    rw [← hc] at this
    simpa using this
  · rw [Td.fil, Td.fil, map_mul, hc]
    exact hF j _

section Abstract

variable {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem map_mem_FilV (K : FinExt l) (j k : ℤ) (g : Pl.R.BdR →ₗ[ℚ_[l]] Pl.R.BdR)
    (hg : ∀ b ∈ (Pl.PD K).Fil j, g b ∈ (Pl.PD K).Fil k) (x : V ⊗[ℚ_[l]] Pl.R.BdR)
    (hx : x ∈ FilV (Pl.PD K) (LL := LL) (V := V) j) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) g x ∈ FilV (Pl.PD K) (LL := LL) (V := V) k := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | tmul v b => exact ⟨v ⊗ₜ ⟨g b.1, hg _ b.2⟩, rfl⟩
  | add y z hy hz => simp only [map_add (f := _)]; exact Submodule.add_mem _ hy hz

theorem map_mulLeft_comp (r s : Pl.R.BdR) (x : V ⊗[ℚ_[l]] Pl.R.BdR) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] r)
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] s) x) =
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] (r * s)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => simp [mul_assoc]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem map_mulLeft_one (x : V ⊗[ℚ_[l]] Pl.R.BdR) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] (1 : Pl.R.BdR)) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

end Abstract

end GlobalTheory.BKReal.EhatShift

namespace GlobalTheory.BKReal.EhatShift

variable {l : ℕ} [Fact l.Prime] {Pl : LocPrime l}
    {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem bijective_and_mem_FilV_iff_of_mul (K : FinExt l) (ξ : Pl.R.BdR) (hu : IsUnit ξ)
    (hF : ∀ (j : ℤ) (x : Pl.R.BdR), x ∈ (Pl.PD K).Fil j ↔ ξ * x ∈ (Pl.PD K).Fil (j + 1))
    (f : V ⊗[ℚ_[l]] Pl.R.BdR →+ V ⊗[ℚ_[l]] Pl.R.BdR) (hf : ∀ v c, f (v ⊗ₜ[ℚ_[l]] c) = v ⊗ₜ[ℚ_[l]] (ξ * c)) :
    Function.Bijective f ∧ ∀ (y : V ⊗[ℚ_[l]] Pl.R.BdR) (j : ℤ),
      y ∈ FilV (Pl.PD K) (LL := LL) (V := V) j ↔ f y ∈ FilV (Pl.PD K) (LL := LL) (V := V) (j + 1) := by
  have hAM : ∀ y, f y = AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] ξ) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v c => rw [hf, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hl : ∀ y, AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (LinearMap.mulLeft ℚ_[l] ((hu.unit⁻¹ : (Pl.R.BdR)ˣ) : Pl.R.BdR)) (f y) = y := fun y => by
    rw [hAM, map_mulLeft_comp, IsUnit.val_inv_mul, map_mulLeft_one]
  have hr : ∀ y, f (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (LinearMap.mulLeft ℚ_[l] ((hu.unit⁻¹ : (Pl.R.BdR)ˣ) : Pl.R.BdR)) y) = y := fun y => by
    rw [hAM, map_mulLeft_comp, IsUnit.mul_val_inv, map_mulLeft_one]
  refine ⟨Function.bijective_iff_has_inverse.2 ⟨_, hl, hr⟩, fun y j => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hAM]
    exact map_mem_FilV K j (j + 1) _ (fun b hb => (hF j b).1 hb) y h
  · have := map_mem_FilV K (j + 1) j
      (LinearMap.mulLeft ℚ_[l] ((hu.unit⁻¹ : (Pl.R.BdR)ˣ) : Pl.R.BdR)) (fun b hb => by
        rw [hF j, LinearMap.mulLeft_apply, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
        exact hb) _ h
    rwa [hl] at this

end GlobalTheory.BKReal.EhatShift


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → Function.Bijective (A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e))) ∧ ∀ (y : T.V ⊗[ℚ_[l]] Pl.R.BdR) (j : ℤ), y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j) ↔ A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j + 1) := by
  intro l _ a e _ _ ϖ LL _ _ T Pl AI Td A hA
  rw [GlobalTheory.BKReal.PiSys.iD_const_Ehat_eq_tmul l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ]
  obtain ⟨hu, hF⟩ := GlobalTheory.BKReal.EhatShift.isUnit_and_mem_Fil_iff Td (a := a) ϖ (Formalism.MainNotions.ElementDenominator.qlExt l)
  refine GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff_of_mul _ _ hu hF _ fun v c => ?_
  rw [hA]
  simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingProductSeriesToTensorBcrisInjectiveFinE
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.IBInj

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
  [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
  [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]


omit [NeZero a] [NeZero e] [Module.Finite ℤ_[l] O] [CompleteSpace K] in
theorem toOB_injective : Function.Injective (toOB l O) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := O) (acrisToBcris l).toLinearMap
    (GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l)


omit [NeZero a] in
theorem iSD_eq_of_mem_invL_A (ϖ : PiSys l e) (f : invL l (S O K e)) (hf : (f : K⟦X⟧) ∈ invL l (A O K)) :
    ϖ.iSD O K f = ϖ.iHat O K (toHatS O K l e f) := by
  obtain ⟨n, hn⟩ := hf
  have hlu : IsUnit ((l : OD l O) ^ n) := isUnit_l_OD.pow n
  have hg : ((l : A O K) : K⟦X⟧) ^ n * (f : K⟦X⟧) ∈ S O K e := A_le_S l e hn
  have e1 : (l : invL l (S O K e)) ^ n * f = algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩ :=
    Subtype.ext (by simp)
  have e2 : toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩) =
      ofA O K l e ⟨_, hn⟩ := toHat_eq_ofAl l e rfl
  refine hlu.mul_left_cancel ?_
  have h3 := congrArg (ϖ.iSD O K) e1
  have h4 := congrArg (fun y => ϖ.iHat O K (toHatS O K l e y)) e1
  simp only [map_mul, map_pow, map_natCast] at h3 h4
  rw [h3, h4, e2, ϖ.iHat_ofA O K]
  refine (ϖ.iSD_of_mem O K hg _).trans ?_
  rw [ϖ.iS_of_mem O K hn, crisToOD_toOCr]


omit [NeZero a] in
theorem crisToOD_iS (ϖ : PiSys l e) (s : S O K e) : crisToOD l O (ϖ.iS O K s) =
    ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) := by
  have hlu : IsUnit (l : OD l O) := isUnit_l_OD
  set ξ : OD l O := ϖ.iAl O K (EIn l e _) with hξ
  have hS : ∀ s : S O K e, ϖ.iSD O K (algebraMap (S O K e) (invL l (S O K e)) s) =
      crisToOD l O (ϖ.iS O K s) := fun s => ϖ.iSD_of_mem O K s.2 _
  rw [← sub_eq_zero]
  set D : S O K e → OD l O := fun s => crisToOD l O (ϖ.iS O K s) -
    ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) with hD
  have hDadd : ∀ p q : S O K e, D (p + q) = D p + D q := fun p q => by
    simp only [hD, map_add (f := _)]; ring
  have hDmul : ∀ (k : ℕ) (q : S O K e), D ((l : S O K e) ^ k * q) = (l : OD l O) ^ k * D q := fun k q => by
    simp only [hD, map_mul, map_pow, map_natCast]; ring
  have hdiv : ∀ m : ℕ, ξ ^ m ∣ D s := by
    intro m
    obtain ⟨N, hN⟩ := GlobalTheory.BKReal.CrisBounded.bdd_crisToOD l e O K ϖ m
    have hw : ∀ k : ℕ, ∃ y : OA l O,
        ξ ^ m ∣ (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O y := by
      intro k
      obtain ⟨N0, hN0⟩ := exists_sum_monomial_add l e s.2 k
      obtain ⟨h, hh, hs⟩ := hN0 N0 le_rfl
      set hS' : S O K e := ⟨h, hh⟩
      have hP : (s : K⟦X⟧) - (l : K⟦X⟧) ^ k * h ∈ S O K e :=
        sub_mem s.2 (mul_mem (pow_mem (natCast_mem _ l) k) hh)
      set P : S O K e := ⟨_, hP⟩
      have hsP : s = P + (l : S O K e) ^ k * hS' := Subtype.ext (by simp [P, hS'])
      have hPA : (P : K⟦X⟧) ∈ invL l (A O K) := by
        have : (P : K⟦X⟧) = ∑ n ∈ Finset.range N0, monomial n (coeff n (s : K⟦X⟧)) := by
          simp only [P]; linear_combination hs
        rw [this]
        exact sum_mem fun n _ => monomial_mem_invL l n _
      have hDP : D P = 0 := by
        simp only [hD, sub_eq_zero]
        rw [← hS]
        exact iSD_eq_of_mem_invL_A ϖ _ hPA
      obtain ⟨y1, hy1⟩ := hN (ϖ.iS O K hS')
      obtain ⟨y2, hy2⟩ := GlobalTheory.BKReal.exists_l_pow_iHat_toHatS_sub_dvd l e O K ϖ m hS'
      refine ⟨(l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2, ?_⟩
      have e1 : (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k *
            toOD l O ((l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2) =
          (l : OD l O) ^ k * ((l : OD l O) ^ m * ((l : OD l O) ^ N * crisToOD l O (ϖ.iS O K hS') -
            toOD l O y1) - (l : OD l O) ^ N * ((l : OD l O) ^ m *
              ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) hS')) - toOD l O y2)) := by
        rw [hsP, hDadd, hDP, zero_add, hDmul]
        simp only [hD, map_sub, map_mul, map_pow, map_natCast]
        ring
      rw [e1]
      exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right hy1 _) (dvd_mul_of_dvd_right hy2 _)) _
    have h1 := GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD l e O K ϖ m _ hw
    rw [pow_add, mul_assoc] at h1
    exact (((hlu.pow N).mul (hlu.pow m)).dvd_mul_left).1 (by rwa [← mul_assoc] at h1)
  have hc := ϖ.complete_OD O K
  exact hc.toIsHausdorff.haus' _ fun n => by
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero]
    exact Ideal.mem_span_singleton.2 (hdiv n)


omit [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NeZero e] [CompleteSpace K] in
theorem eq_zero_of_forall_dvd (x : Ahat O K l e) (h : ∀ n : ℕ, ∃ y, x = Ehat O K l e ^ n * y) : x = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, rfl⟩ := h n
  have hE : AdicCompletion.evalₐ (idE O K l e) n (Ehat O K l e) = Ideal.Quotient.mk _ (EIn l e _) :=
    AlgHom.commutes _ _
  rw [map_mul, map_pow, hE, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n), zero_mul]
  exact (map_zero _).symm

theorem eq_zero_of_idem_mul_iS (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (τ : ZMod a) (s : S O K e)
    (h : idem (constC t) τ * ϖ.iS O K s = 0) : s = 0 := by
  set x := toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s) with hx
  have h1 : idem (constD t) τ * ϖ.iHat O K x = 0 := by
    have h2 := congrArg (crisToOD l O) h
    rw [map_mul, map_zero, crisToOD_iS ϖ s] at h2
    have h3 : crisToOD l O (idem (constC t) τ) = idem (constD t) τ :=
      crisToOD_toOCr (constA t (Pi.single τ 1))
    rwa [h3] at h2
  have h4 : ϖ.iD t K (Pi.single τ x) = 0 := by
    rw [PiSys.iD, glue_apply, Finset.sum_eq_single τ (fun σ _ hσ => by
      rw [Pi.single_eq_of_ne hσ, map_zero, mul_zero]) (by simp), Pi.single_eq_same, h1]
  have h5 : x = 0 := eq_zero_of_forall_dvd x fun n => by
    obtain ⟨y, hy⟩ := GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem l a e O K t ϖ n (Pi.single τ x)
      (by rw [h4]; exact zero_mem _)
    exact ⟨y τ, by simpa using congrFun hy τ⟩
  have h6 : toHat O K l e ⟨(s : K⟦X⟧), invL_S_le_Rpi l e (le_away _ _ s.2)⟩ = 0 := h5
  have h7 := GlobalTheory.BK.toHat_injective O K l e (h6.trans (map_zero _).symm)
  have h8 : (s : K⟦X⟧) = 0 := congrArg (fun z : Rpi O K l e => (z : K⟦X⟧)) h7
  exact Subtype.ext h8

theorem iB_injective (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) : Function.Injective (ϖ.iB t K) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => funext fun τ => ?_
  obtain ⟨k, hk⟩ := (x τ).2
  set s : S O K e := ⟨_, hk⟩
  have hs : algebraMap (S O K e) (invL l (S O K e)) s = (l : invL l (S O K e)) ^ k * x τ :=
    Subtype.ext (by simp [s])
  have h1 := idem_mul_glue (constB t) (ϖ.iSl O K) x τ
  rw [show glue (constB t) (ϖ.iSl O K) x = 0 from hx, mul_zero] at h1
  have h3 : ϖ.iSl O K (algebraMap (S O K e) (invL l (S O K e)) s) = toOB l O (ϖ.iS O K s) :=
    ϖ.iSl_of_mem O K s.2 _
  have h2 : toOB l O (idem (constC t) τ * ϖ.iS O K s) = 0 := by
    rw [map_mul, ← h3, hs, map_mul, map_pow, map_natCast]
    change idem (constB t) τ * (_ * _) = 0
    rw [mul_left_comm, ← h1, mul_zero]
  have h4 : idem (constC t) τ * ϖ.iS O K s = 0 := toOB_injective (h2.trans (map_zero _).symm)
  have h5 := eq_zero_of_idem_mul_iS t ϖ τ s h4
  have h6 : (l : invL l (S O K e)) ^ k * x τ = 0 := by rw [← hs, h5, map_zero]
  have h7 : (l : K⟦X⟧) ^ k * (x τ : K⟦X⟧) = 0 := by simpa using congrArg Subtype.val h6
  have hl0 : (l : K⟦X⟧) ≠ 0 := fun h0 => BK.l_ne_zero (K := K) l (by
    simpa using congrArg PowerSeries.constantCoeff h0)
  exact Subtype.ext ((mul_eq_zero.1 h7).resolve_left (pow_ne_zero _ hl0))

theorem iB_injective_finExt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (LL : FinExt l)
    (t : Wq l a →ₐ[ℤ_[l]] ↥(OL LL)) (ϖ : PiSys l e), Function.Injective (ϖ.iB t ↥LL.1) :=
  fun _ _ _ _ _ _ _ t ϖ => iB_injective t ϖ

end GlobalTheory.BKReal.IBInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionBreuilKisinHomStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedDisc_extension_breuilKisinHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ ≤ 1 → ∃ F : bk.DS ρ →+* Disc l (BK.hf f X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) F := by
  first | exact @GlobalTheory.BSP.DiscPrism.disc_map_exists | exact GlobalTheory.BSP.DiscPrism.disc_map_exists | (intros; apply GlobalTheory.BSP.DiscPrism.disc_map_exists <;> assumption)
end

