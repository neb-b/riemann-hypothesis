module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0234
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0196

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpMultiplicityRestrictFiniteExt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.JumpRestrict

open GlobalTheory.DRFil

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_inclusion (P : LocPrime l) {K K' : FinExt l} (h : K.1 ≤ K'.1) (c : ↥K.1) :
    algebraMap ↥K'.1 P.R.BdR (IntermediateField.inclusion h c) = algebraMap ↥K.1 P.R.BdR c := rfl

theorem idem_restrict_mul (P : LocPrime l) {K K' LL : FinExt l} (h : K.1 ≤ K'.1)
    (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) :
    haveI := K.2; haveI := K'.2
    idem (K := ↥K.1) P.R.BdR (τ.comp (IntermediateField.inclusion h)) * idem (K := ↥K'.1) P.R.BdR τ =
      idem (K := ↥K'.1) P.R.BdR τ := by
  haveI := K.2; haveI := K'.2
  obtain ⟨n, a, c, hrep, h1⟩ := idem_repr (K := ↥K.1) P.R.BdR (τ.comp (IntermediateField.inclusion h))
  have e := exists_smul_idem (K := ↥K'.1) (F := P.R.BdR) τ n a (fun i => IntermediateField.inclusion h (c i))
  simp only [algebraMap_inclusion] at e
  rw [hrep, mul_comm, e]
  simp only [AlgHom.comp_apply] at h1
  rw [h1, one_smul]

theorem multV_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) τ a = multV (P.PD K) ρ (τ.comp (IntermediateField.inclusion h)) a := by
  intro l _ P AI T K K' LL h V _ _ _ _ _ ρ hdr τ a
  haveI := K.2; haveI := K'.2; haveI := LL.2
  haveI := (_root_.GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  obtain ⟨m, d, k, hA⟩ := exists_adapted (P.PD K) (isField_dR T) ρ (filSpans T K LL ρ hdr)
    (τ.comp (IntermediateField.inclusion h))
  have hI := idem_restrict_mul P h τ
  have hA' : Adapted (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) τ
      (fun i => sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR τ) (d i)) k := by
    refine ⟨fun i => ?_, fun r hr i => ?_, fun n y hy => ?_⟩
    · have hm := hA.mem i
      refine ⟨sm_idem_mem_DdRE (P.PD K') _ τ
        (GlobalTheory.Per.TiedRestrict.ddR_le h ρ (Submodule.mem_inf.1 (Submodule.mem_inf.1 hm).1).1), ?_⟩
      refine sm_idem_mem_FilV (P.PD K') τ ?_
      rw [GlobalTheory.JumpDescent.FilV_eq P K K']
      exact (Submodule.mem_inf.1 hm).2
    · have := hA.indep (fun i => r i * idem P.R.BdR τ) (by
        simpa only [sm_mul] using hr) i
      rw [mul_left_comm, hI] at this
      rw [mul_comm]; exact this
    · rw [GlobalTheory.JumpDescent.FilV_eq P K K'] at hy
      obtain ⟨r, hr, hy'⟩ := hA.span n y hy
      refine ⟨r, fun i => ?_, ?_⟩
      · rw [GlobalTheory.JumpDescent.FilV_eq P K K']; exact hr i
      · have e : sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR τ) y = sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR τ)
            (sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR (τ.comp (IntermediateField.inclusion h))) y) := by
          rw [← sm_mul, mul_comm, hI]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [e, hy', map_sum]
        exact Finset.sum_congr rfl fun i _ => sm_comm _ _ _
  rw [hA.multV_eq, hA'.multV_eq]

end GlobalTheory.JumpRestrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixEquivariant
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis

noncomputable section

namespace GlobalTheory.HTBasis

open GlobalTheory.DeRhamSymbol GlobalTheory.DeRhamSymbolBasis

theorem colHT_equivariant : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K LL : FinExt l} {m : ℕ} (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → ∀ g : ↥(GK K), (∀ i, ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec (fun j => P.actQdR (g : GQ l) (u i j)) = u i) → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (colHT J u k).map (Per.σC (g : GQ l)) = colHT J u k * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  intro l _ P AI J K LL m r' u k hu g hg
  ext j i
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Matrix.map_apply, colHT, Matrix.of_apply]
  set M := (r' g : Matrix (Fin m) (Fin m) ↥LL.1) with hM
  set t : P.R.BdR := ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) with ht
  set q : ℚ_[l] := ((P.χQ (g : GQ l) ^ k i : ℚ_[l]ˣ) : ℚ_[l]) with hq
  have key : ∀ x, t * u i x ∈ (P.PD (Formalism.MainNotions.LocalSituation.botExt l)).Fil 0 := fun x =>
    (shift_iff J (k i) 0 _).2 (by rw [add_zero]; exact (mem_iff K _ _).1 (hu i x))
  have hmem : ∀ x, algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x) ∈
      (P.PD (Formalism.MainNotions.LocalSituation.botExt l)).Fil 0 := fun x => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]
    exact om_mul_mem _ (act_mem _ (key x))
  have h1 := congrFun (hg i) j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, embF_apply] at h1
  have h2 : t * u i j = ∑ x, algebraMap (Om l) P.R.BdR ((M j x : ↥LL.1) : Om l) *
      (algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x)) := by
    conv_lhs => rw [← h1]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_left_comm, shift_act]
  have h3 : ∀ x, J.θ (algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x)) =
      (q : ℂ_[l]) * Per.σC (g : GQ l) (J.θ (t * u i x)) := fun x => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR,
      J.θ_mul _ (om_mem _) _ (act_mem _ (key x)), J.θ_Om, J.θ_act _ _ (key x),
      GlobalTheory.MemLoc.TiedTheta.actC_eq]
  have hunit : (q : ℂ_[l]) * ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = 1 := by
    have e : q * (((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) = 1 := by
      rw [hq, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
    have e2 := congrArg (fun z : ℚ_[l] => (z : ℂ_[l])) e
    rw [map_mul, UniformSpace.Completion.coe_mul, map_one, UniformSpace.Completion.coe_one] at e2
    exact e2
  rw [h2, theta_comb J _ _ hmem, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h3]
  linear_combination (-((((M j x : ↥LL.1) : Om l) : ℂ_[l]) * Per.σC (g : GQ l) (J.θ (t * u i x)))) * hunit

end GlobalTheory.HTBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixIsUnitDet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis

noncomputable section

namespace GlobalTheory.HTBasis

open GlobalTheory.DeRhamSymbol Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem colHT_isUnit_det {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
    (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K : FinExt l} {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ)
    (hu : ∀ i j, u i j ∈ (P.PD K).Fil (k i))
    (hspan : ∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) →
      ∃ f : Fin m → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u i)
    (hli : LinearIndependent P.R.BdR u) : IsUnit (colHT J u k).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hc0
  set s : Fin m → Fin m → P.R.BdR := fun i j => ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) * u i j with hs
  have hs0 : ∀ i j, s i j ∈ (P.PD (botExt l)).Fil 0 := fun i j =>
    (shift_iff J (k i) 0 _).2 (by rw [add_zero]; exact (mem_iff K _ _).1 (hu i j))
  choose γ hγ0 hγ using J.θ_onto
  set z : Fin m → P.R.BdR := fun j => ∑ i, γ (c i) * s i j with hz
  have hz0 : ∀ j, z j ∈ (P.PD (botExt l)).Fil 0 := fun j => by
    have := Submodule.sum_mem ((P.PD (botExt l)).Fil 0) (t := Finset.univ)
      (f := fun i => γ (c i) * s i j) fun i _ => by
        simpa using (P.PD (botExt l)).Fil_mul 0 0 _ _ (hγ0 (c i)) (hs0 i j)
    exact this
  have hz1 : ∀ j, z j ∈ (P.PD K).Fil 1 := fun j => by
    rw [mem_iff K]
    refine (J.θ_ker _ (hz0 j)).1 ?_
    have h1 := congrFun hc j
    simp only [Matrix.mulVec, dotProduct, colHT, Matrix.of_apply, Pi.zero_apply] at h1
    rw [hz, GlobalTheory.DeRhamSymbolBasis.theta_sum J _ _ fun i => by
      simpa using (P.PD (botExt l)).Fil_mul 0 0 _ _ (hγ0 (c i)) (hs0 i j)]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [J.θ_mul _ (hγ0 (c i)) _ (hs0 i j), hγ, mul_comm]
  obtain ⟨f, hf, hfz⟩ := hspan 1 z hz1
  have hz' : z = ∑ i, (γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR)) • u i := by
    funext j
    simp only [hz, hs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hdiff := Fintype.linearIndependent_iff.1 hli
    (fun i => f i - γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR)) (by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hfz, ← hz', sub_self])
  funext i
  have hfi : f i = γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) := sub_eq_zero.1 (hdiff i)
  have hγi : γ (c i) = f i * ((tU P ^ (k i) : P.R.BdRˣ) : P.R.BdR) := by
    rw [hfi, mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, mul_one]
  have hmem : γ (c i) ∈ (P.PD (botExt l)).Fil 1 := by
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ ((mem_iff K _ _).1 (hf i)) (zpow_mem J (k i))
    rw [sub_add_cancel] at this
    rwa [hγi]
  rw [Pi.zero_apply, ← hγ (c i)]
  exact (J.θ_ker _ (hγ0 (c i))).2 hmem

end GlobalTheory.HTBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsVanishAtPrimeOfAdmissible
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.InvKilled

variable {l : ℕ} [Fact l.Prime]

theorem exists_pow_smul_mem (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (v : T.V) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.IntegerRingPowers.main
  | exact _root_.GlobalTheory.IntegerRingPowers.main
  | (apply _root_.GlobalTheory.IntegerRingPowers.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerRingPowers.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerRingPowers.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerRingPowers.main ..)

theorem killed_of_coordinates {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [CharZero LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) [Module ℤ_[l] ↥T.L.T]
    (hsm : ∀ (k : ℕ) (t : ↥T.L.T),
      ((((l : ℤ_[l]) ^ k) • t : ↥T.L.T) : T.V) = (l : LL) ^ k • (t : T.V))
    (ac : G → (↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T)) (hac : ∀ g t, ((ac g t : ↥T.L.T) : T.V) = T.ρ g t)
    {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] ↥T.L.T)
    (M : G → Matrix (Fin d) (Fin d) (PadicComplex l))
    (hb : ∀ g i j, M g i j = zC (b.repr (ac g (b j)) i)) (c : ℕ)
    (H : ∀ y : Fin d → ℚ_[l], (∀ σ,
      (M σ).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) -
        (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ ball l d) →
      ∀ a, ‖(l : ℚ_[l]) ^ c * y a‖ ≤ 1)
    (v : T.V) (hw : ∀ g, T.ρ g v - v ∈ T.L.T) (n : ℕ) (hn : (l : LL) ^ n • v ∈ T.L.T) :
    (l : LL) ^ c • v ∈ T.L.T := by
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlL : (l : LL) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set t : ↥T.L.T := ⟨_, hn⟩ with ht
  have hy := H (fun a => ((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l])) (by
    intro σ a
    have e1 : ac σ t - t = (l : ℤ_[l]) ^ n • (⟨_, hw σ⟩ : ↥T.L.T) := by
      apply Subtype.ext
      rw [hsm, Submodule.coe_sub, hac]
      change T.ρ σ ((l : LL) ^ n • v) - (l : LL) ^ n • v = _
      rw [map_smul, smul_sub]
    have e2 : b.repr (ac σ t) a =
        ∑ j, b.repr (ac σ (b j)) a * b.repr t j := by
      conv_lhs => rw [← b.sum_repr t]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply,
        smul_eq_mul, mul_comm]
    have e3 := congrArg (fun z => ((b.repr z a : ℤ_[l]) : ℚ_[l])) e1
    simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, e2] at e3
    push_cast at e3
    have e4 : ((M σ).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l)
          (((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l]))) -
        (fun a => algebraMap ℚ_[l] (PadicComplex l) (((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l])))) a =
        algebraMap ℚ_[l] (PadicComplex l) ((b.repr (⟨_, hw σ⟩ : ↥T.L.T) a : ℤ_[l]) : ℚ_[l]) := by
      have hb' : ∀ i j, M σ i j = zC (b.repr (ac σ (b j)) i) := hb σ
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, hb', zC, ← map_mul, ← map_sum, ← map_sub]
      congr 1
      have hp : (l : ℚ_[l]) ^ n ≠ 0 := pow_ne_zero _ hl
      rw [← inv_mul_cancel_left₀ hp (((b.repr (⟨_, hw σ⟩ : ↥T.L.T) a : ℤ_[l]) : ℚ_[l])), ← e3,
        mul_sub, PadicInt.coe_sum, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [PadicInt.coe_mul]; ring
    rw [e4, norm_algebraMap']
    exact PadicInt.norm_le_one _)
  let z : Fin d → ℤ_[l] := fun a => ⟨_, hy a⟩
  let t' : ↥T.L.T := ∑ a, z a • b a
  have e5 : (l : ℤ_[l]) ^ c • t = (l : ℤ_[l]) ^ n • t' := by
    apply b.repr.injective
    ext a
    have : b.repr t' a = z a := congrFun (b.repr_sum_self z) a
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, this]
    have hz : ((z a : ℤ_[l]) : ℚ_[l]) = (l : ℚ_[l]) ^ c * (((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l])) := rfl
    rw [PadicInt.coe_mul, PadicInt.coe_mul, hz]
    push_cast
    field_simp
  have e6 := congrArg Subtype.val e5
  rw [hsm, hsm] at e6
  change (l : LL) ^ c • (l : LL) ^ n • v = _ at e6
  rw [smul_comm] at e6
  have e7 := smul_right_injective _ (pow_ne_zero n hlL) e6
  rw [e7]
  exact t'.2

theorem pow_smul_compHom {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) (φ : ℤ_[l] →+* O) :
    letI : Module ℤ_[l] ↥T.L.T := Module.compHom ↥T.L.T φ
    ∀ (k : ℕ) (t : ↥T.L.T),
      ((((l : ℤ_[l]) ^ k) • t : ↥T.L.T) : T.V) = (l : LL) ^ k • (t : T.V) := by
  intro k t
  change (φ ((l : ℤ_[l]) ^ k)) • (t : T.V) = _
  rw [← algebraMap_smul LL, map_pow, map_natCast, map_pow, map_natCast]

theorem killed_of_coord (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (hM : IsMat K LL T M A) (c : ℕ)
    (H : ∀ y : Fin d → ℚ_[l], (∀ σ ∈ GK K,
      (M σ).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) -
        (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ ball l d) →
      ∀ a, ‖(l : ℚ_[l]) ^ c * y a‖ ≤ 1)
    (v : T.V) (hw : ∀ g : ↥(GK K), T.ρ g v - v ∈ T.L.T) : (l : ↥LL.1) ^ c • v ∈ T.L.T := by
  obtain ⟨b, hb, -⟩ := hM
  obtain ⟨n, hn⟩ := exists_pow_smul_mem K LL T v
  refine @killed_of_coordinates l _ _ _ _ _ _ _ _ _ _ _ _ _ _ T (zlMod LL T) ?_
    (fun g => actTZ LL T g) (fun _ _ => rfl) d b (fun g => M g) hb c
    (fun y hy => H y fun σ hσ => hy ⟨σ, hσ⟩) v hw n hn
  exact pow_smul_compHom T (algebraMap ℤ_[l] ↥(OL LL))

theorem killed_quot {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O)
    (p c : ℕ) (H : ∀ v : T.V, (∀ g, T.ρ g v - v ∈ T.L.T) → (p : LL) ^ c • v ∈ T.L.T)
    (x : T.V ⧸ T.L.T) (hx : ∀ g, actD T.L g x = x) : ((p : O) ^ c) • x = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL, map_pow,
    map_natCast]
  exact H v fun g => (Submodule.Quotient.eq _).1 (hx g)

def imBall {r d : ℕ} (P : Matrix (Fin r) (Fin d) (PadicComplex l)) :
    AddSubgroup (Fin r → PadicComplex l) where
  carrier := P.mulVec '' ball l d
  zero_mem' := ⟨0, fun a => by simp, Matrix.mulVec_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, fun a => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx a) (hy a)),
      Matrix.mulVec_add _ _ _⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, fun a => by simpa using hx a, Matrix.mulVec_neg _ _⟩

theorem Ks_mono' (K : FinExt l) {i j : ℕ} (h : i ≤ j) : Ks K i ≤ Ks K j := by
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
  intro x hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [pow_add, pow_mul, hx, one_pow]

theorem act_algebraMap' {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (g : GQ l) (x : ℚ_[l]) :
    act g (algebraMap ℚ_[l] (PadicComplex l) x) = algebraMap ℚ_[l] (PadicComplex l) x := by
  have := ha.1 g (algebraMap ℚ_[l] (Om l) x)
  rw [AlgEquiv.commutes] at this
  exact this

theorem invariants_killed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; H0at S E := by
  intro D HW F h7 l _ K s LL h S E M0 h0 T τ hW hj x hx
  have hell : ell S = l := (D.loc l).PD_p K
  have hs : S.W.s = s := (HW l).W_s K s LL h
  obtain ⟨d, M, A, hM⟩ := (_root_.GlobalTheory.Cyc.isMat_exists_and_props l K LL T).1
  obtain ⟨r, P, U, g, J, hJ, hfin, hFr, hHT, hPM, hb1, hb2, hint⟩ :=
    GlobalTheory.T.exists_tau_component_frame_of_lattice D HW F h7 l K s LL h T M0 h0 τ hW d M A hM
  have hact : IsActC (D.locA l).actC := ⟨(D.locA l).actC_ext, (D.locA l).actC_norm⟩
  have hχ : IsCyc (D.loc l).χQ := (D.loc l).χQ_cyc
  set m := mN l s (M0 + h0) with hm
  have hsm : s + 1 ≤ m := by rw [hm, mN]; omega
  have hs1 := h.1
  have hLev : Lev l m := ⟨by omega, fun _ => by omega⟩
  have hG : Gj K m ≤ GK K :=
    IntermediateField.fixingSubgroup_le (h.2.2.1.trans (Ks_mono' K (by omega)))
  have h0J : (0 : ℤ) ∉ J := fun hh => hj (hJ 0 hh)
  have hc0 : c0 S T τ M0 h0 = 2 + ∑ u ∈ hfin.toFinset, (m + padicValInt l u) := by
    rw [c0, hell, hs]
    congr 1
    exact finsum_mem_eq_finite_toFinset_sum (fun u => m + vZ l u) hfin
  rw [hell]
  refine killed_quot T l _ (killed_of_coord K LL T M A hM _ ?_) x hx
  intro y hy
  have hl1 : ‖(l : ℚ_[l])‖ ≤ 1 := (Padic.norm_p_lt_one).le
  rcases J.eq_empty_or_nonempty with rfl | ⟨u0, hu0⟩
  · obtain ⟨e, u, -, hu, -⟩ := hHT
    have : IsEmpty (Fin r) := ⟨fun k => by simpa using hu k⟩
    intro a
    have := hint y ⟨0, fun a => by simp, Subsingleton.elim _ _⟩ a
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1) (norm_nonneg _) this
  · have key := GlobalTheory.T.prime_pow_smul_mem_of_twistedInvariant_mod_lattice l _ _ hact hχ K m r hLev U g hFr J hHT 0 h0J (imBall P) hb1
      (by rintro _ ⟨z, hz, rfl⟩; exact hb2 z hz)
      (P.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a))) (by
        intro σ hσ
        refine ⟨_, hy σ (hG hσ), ?_⟩
        have e1 : (fun a => (D.locA l).actC σ
            (P.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) a)) =
            (P.map ((D.locA l).actC σ)).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) := by
          funext a
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply,
            act_algebraMap' hact]
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPM σ hσ, twAct, e1, Matrix.mulVec_mulVec]
        simp [chiC])
    rw [Finset.erase_eq_of_notMem h0J] at key
    simp only [sub_zero] at key
    have hle1 : 1 ≤ ∑ u ∈ J, (m + padicValInt l u) :=
      le_trans (by omega) (Finset.single_le_sum (f := fun u => m + padicValInt l u)
        (fun _ _ => Nat.zero_le _) hu0)
    have hle2 : ∑ u ∈ J, (m + padicValInt l u) ≤ ∑ u ∈ hfin.toFinset, (m + padicValInt l u) :=
      Finset.sum_le_sum_of_subset fun u hu => hfin.mem_toFinset.2 (hJ u hu)
    rw [max_eq_right hle1] at key
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle2
    have hi := hint (fun a => (l : ℚ_[l]) ^ (2 + ∑ u ∈ J, (m + padicValInt l u)) * y a) (by
      have e : (fun a => algebraMap ℚ_[l] (PadicComplex l)
          ((l : ℚ_[l]) ^ (2 + ∑ u ∈ J, (m + padicValInt l u)) * y a)) =
          (l : PadicComplex l) ^ (2 + ∑ u ∈ J, (m + padicValInt l u)) •
            (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) := by
        funext a
        simp only [map_mul, map_pow, map_natCast, Pi.smul_apply, smul_eq_mul]
      rw [e, Matrix.mulVec_smul]
      exact key)
    intro a
    rw [hc0, hk, ← add_assoc, add_comm _ k, pow_add, mul_assoc, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1) (norm_nonneg _) (hi a)

end GlobalTheory.Cyc.InvKilled
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeOfIsBaseChangeQuotient
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isBaseChange_of_isBaseChange_quotient :
    ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (𝔞 : Ideal S), 𝔞 ≤ Ideal.jacobson ⊥ → ∀ (P : Type) [AddCommGroup P] [Module R P] [Module.Finite R P] (V : Type) [AddCommGroup V] [Module S V] [Module R V] [IsScalarTower R S V] [Module.Finite S V] [Module.Projective S V] (W : Type) [AddCommGroup W] [Module (S ⧸ 𝔞) W] [Module S W] [Module R W] [IsScalarTower S (S ⧸ 𝔞) W] [IsScalarTower R (S ⧸ 𝔞) W] [IsScalarTower R S W] (u : P →ₗ[R] V) (g : V →ₗ[S] W), IsBaseChange (S ⧸ 𝔞) g → IsBaseChange (S ⧸ 𝔞) (g.restrictScalars R ∘ₗ u) → IsBaseChange S u := by
  intro R S _ _ _ 𝔞 h𝔞 P _ _ _ V _ _ _ _ _ _ W _ _ _ _ _ _ _ u g hg hgu
  have hF : IsBaseChange S (TensorProduct.mk R S P 1) := TensorProduct.isBaseChange R P S
  let w : S ⊗[R] P →ₗ[S] V := hF.lift u
  have hw : ∀ x : P, w (1 ⊗ₜ[R] x) = u x := fun x => hF.lift_eq u x
  have hcomp : (g ∘ₗ w).restrictScalars R ∘ₗ TensorProduct.mk R S P 1 = g.restrictScalars R ∘ₗ u := by
    ext x
    simp [hw]
  have hgw : IsBaseChange (S ⧸ 𝔞) (g ∘ₗ w) := hF.of_comp (hcomp ▸ hgu)
  have heq : ∀ z, hg.equiv (w.baseChange (S ⧸ 𝔞) z) = hgw.equiv z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
      rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
  have hfun : ⇑(w.baseChange (S ⧸ 𝔞)) = hg.equiv.symm ∘ hgw.equiv := by
    funext z
    simp [← heq z]
  have hbij : Function.Bijective (w.baseChange (S ⧸ 𝔞)) := by
    rw [hfun]
    exact hg.equiv.symm.bijective.comp hgw.equiv.bijective
  have hwb : Function.Bijective w := GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient S 𝔞 h𝔞 (S ⊗[R] P) V w hbij
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective w hwb) (fun x => hw x)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOnOfIsCrys
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CrysOnLevel

theorem isCrysOn_of_isCrys : ∀ (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (Y : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) Y.ρ → Formalism.MainNotions.LocalSituation.IsCrysOn (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((HW l).W K s LL h).GKs Y := by
  intro D HW l _ K s LL h Y hY
  exact (GlobalTheory.TorsionBoundCompare.crys_iff D.loc HW (D.locA l) h Y).mpr
    ((_root_.GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (D.loc l) (D.locA l) (D.locT l) K (GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.levelField K s) LL h.2.2.1
      Y.V Y.ρ).1 hY)

end GlobalTheory.CrysOnLevel
end

