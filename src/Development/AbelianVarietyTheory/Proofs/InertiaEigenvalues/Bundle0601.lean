module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupProductFiniteClassesCoboundary
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0593
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0594
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCocycleDimensionCompare
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoOrth

open GlobalTheory.BKOrth

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem pairT_filV_right (P : V →ₗ[LL] V' →ₗ[LL] LL) (a : ℤ) (v : V) (z : V' ⊗[Qp] BdR)
    (hz : z ∈ FilV PD (LL := LL) (V := V') a) :
    pairT BdR P (v ⊗ₜ[Qp] (1 : BdR)) z ∈ FilV PD (LL := LL) (V := LL) a := by
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [map_add (f := _)]; exact add_mem hy hy'
  | tmul v' f =>
    rw [AlgebraTensorModule.map_tmul, pairT_tmul, one_mul]
    exact ⟨P v v' ⊗ₜ[Qp] f, rfl⟩

theorem actVB_one (ρ : Representation LL G V) (x : V ⊗[Qp] B) : actVB PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v b => simp [actVB_tmul]

end Gen

theorem cocycle_inv {G : Type} [Group G] {LL V : Type} [Field LL] [AddCommGroup V] [Module LL V]
    (ρ : Representation LL G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (g : G) :
    ρ g (c g⁻¹) = - c g := by
  have h1 : c 1 = 0 := by simpa using hc 1 1
  have := hc g g⁻¹
  rw [mul_inv_cancel, h1] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem goodO_Zl (l : ℕ) [Fact l.Prime] : GoodO (Qp := ℚ_[l]) ℚ_[l] ℤ_[l] := by
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  exact (PadicInt.isOpenEmbedding_coe (p := l)).isOpen_range


set_option maxHeartbeats 1600000 in
theorem orth_of_cont (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V']
    [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V']
    [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V')
    (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]) (hρ' : ∀ y, Continuous fun g => ρ' g y)
    (hdR : IsDR (P.PD K) ρ') (hD : IsDual1 (P.PD K) ρ ρ' m)
    (hχ : Continuous fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]))
    (c : ↥(GK K) → V) (hc : c ∈ geometricCocycles (P.PD K) ρ) (a : ↥(GK K) → V')
    (ha : a ∈ crystallineCocycles (P.PD K) ρ') : CobL (P.PD K) (cupL ρ' m c a) := by
  letI : Module ℤ_[l] V' := Module.compHom V' (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨hcz, b, hb⟩ := hc
  obtain ⟨haz, β, hβφ, hβ⟩ := ha
  obtain ⟨-, d, hd, hd'⟩ :=
    GlobalTheory.CobCrisLift.coboundary_lift l P AI hT K ℚ_[l] ℤ_[l] (goodO_Zl l)
      { V := V', ρ := ρ', cont := hρ' } hdR a β hβ
  have hfixd : ∀ g, actVdR (P.PD K) ρ' g d = d := fun g => by
    have := (Submodule.mem_iInf _).1 hd g
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
  obtain ⟨hsurj, hker⟩ := GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI hT K ℚ_[l] ℚ_[l]
  obtain ⟨we, w0, hw0, hweφ, hweι⟩ := hsurj 0 (pairT P.R.BdR m b d)
  have hweφ' : φVB (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) we = we := (sub_eq_zero.1 hweφ).symm
  let F : ↥(GK K) → ℚ_[l] ⊗[ℚ_[l]] P.R.B := fun h =>
    (actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) h we - we) -
      pairT P.R.B m (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' h β)
  have hFφ : ∀ h, φVB (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) (F h) = F h := fun h => by
    have e1 : φVB (P.PD K) (LL := ℚ_[l]) (V := V) (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
        c h ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
      simp [φVB]
    simp only [F, map_sub, pairT_φVB, e1, GlobalTheory.CobCrisLift.φVB_act, hβφ, hweφ']
  have hFι : ∀ h, ιV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) (F h) ∈
      FilV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) 0 := fun h => by
    have e1 : ιV (P.PD K) (LL := ℚ_[l]) (V := V) (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
        c h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
      simp [ιV]
    have e2 : pairT P.R.BdR m (c h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) (actVdR (P.PD K) ρ' h d) =
        actVdR (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) h (pairT P.R.BdR m b d) -
          pairT P.R.BdR m b d := by
      rw [hb h, map_sub, LinearMap.sub_apply, ← pairT_actVdR (P.PD K) ρ ρ' m hD.1 h b d, hfixd h]
    have hι1 : ιV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) we = pairT P.R.BdR m b d + w0 :=
      sub_eq_iff_eq_add.1 hweι
    have s1 : ιV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) (F h) =
        (actVdR (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) h w0 - w0) -
          pairT P.R.BdR m (c h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR))
            (actVdR (P.PD K) ρ' h (ιV (P.PD K) (LL := ℚ_[l]) (V := V') β - d)) := by
      simp only [F, map_sub, pairT_ιV, e1, GlobalTheory.CobCrisLift.ιV_act, hι1, map_add (f := _), e2]
      abel
    rw [s1]
    exact sub_mem (sub_mem (actVdR_filV (P.PD K) _ 0 h w0 hw0) hw0)
      (pairT_filV_right (P.PD K) m 0 (c h) _ (actVdR_filV (P.PD K) ρ' 0 h _ hd'))
  have hF : ∀ h, ∃ x : ℚ_[l], F h = x ⊗ₜ[ℚ_[l]] (1 : P.R.B) := fun h => hker (F h) (hFφ h) (hFι h)
  choose f hf using hF
  let bas := Module.finBasis ℚ_[l] V
  let γ : Fin (finrank ℚ_[l] V) → ↥(GK K) → ℚ_[l] := fun i g => bas.coord i (c g)
  have hγ : ∀ i, Continuous (γ i) := fun i =>
    (IsModuleTopology.continuous_of_linearMap (bas.coord i)).comp hcz.1
  let k : ↥(GK K) → ℚ_[l] := fun h => charRep (cycLL (P.PD K) ℚ_[l]) h (f h⁻¹)
  have hsum : ∀ g, k g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      ∑ i, γ i g • pairT P.R.B m (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) β +
        (actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (-we) - -we) := by
    intro g
    have ec : c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = ∑ i, γ i g • (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) := by
      conv_lhs => rw [← bas.sum_repr (c g)]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul']
      rfl
    have ek : k g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
        actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (F g⁻¹) := by
      rw [hf g⁻¹, actVB_tmul, map_one]
    have e3 : actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g
        (pairT P.R.B m (c g⁻¹ ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g⁻¹ β)) =
        -pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) β := by
      rw [← pairT_actVB (P.PD K) ρ ρ' m hD.1 g, ← actVB_mul, mul_inv_cancel, actVB_one, actVB_tmul,
        map_one, cocycle_inv ρ c hcz.2 g, neg_tmul, map_neg, LinearMap.neg_apply]
    have e4 : actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g
        (actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g⁻¹ we) = we := by
      rw [← actVB_mul, mul_inv_cancel, actVB_one]
    rw [ek]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, map_sub, e3, e4, map_neg, ec, map_sum, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply]
    abel
  have hk : Continuous k :=
    GlobalTheory.FundCont.contCore_tied l P AI hT K ℚ_[l] ℤ_[l] (goodO_Zl l)
      (charGRep (Qp := ℚ_[l]) (O := ℤ_[l]) (cycLL (P.PD K) ℚ_[l]) hχ) _
      (fun i => pairT P.R.B m (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) β) γ hγ (-we) k hsum
  have hfk : f = fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * k g⁻¹ := by
    funext g
    simp only [k, charRep_apply, inv_inv]
    rw [← mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mul]
  have hcont : Continuous f := by
    rw [hfk]
    exact hχ.mul (hk.comp continuous_inv)
  refine ⟨f, hcont, ?_⟩
  funext ⟨g, h⟩
  have hcup : cupL ρ' m c a (g, h) = m (c g) (ρ' g (a h)) := rfl
  rw [hcup]
  apply tmul_one_injective (P.PD K) (LL := ℚ_[l])
  beta_reduce
  have hd1 : ReciprocityTheory.Def.d1 (charRep (cycLL (P.PD K) ℚ_[l])) f (g, h) =
      charRep (cycLL (P.PD K) ℚ_[l]) g (f h) - f (g * h) + f g := rfl
  have hact : (charRep (cycLL (P.PD K) ℚ_[l]) g (f h)) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (f h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) := by
    rw [actVB_tmul, map_one]
  have hch : actVB (P.PD K) ρ g (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) = ρ g (c h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    rw [actVB_tmul, map_one]
  have hcoc : c (g * h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) + ρ g (c h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    rw [hcz.2 g h, add_tmul]
  have hrhs : (m (c g) (ρ' g (a h))) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B))
          (actVB (P.PD K) ρ' g (actVB (P.PD K) ρ' h β)) -
        pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g β) := by
    have e : (m (c g) (ρ' g (a h))) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
        pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g (a h ⊗ₜ[ℚ_[l]] (1 : P.R.B))) := by
      rw [actVB_tmul, map_one, pairT_tmul, mul_one]
    rw [e, hβ h, map_sub, map_sub]
  have main : actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (F h) - F (g * h) + F g =
      pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B))
          (actVB (P.PD K) ρ' g (actVB (P.PD K) ρ' h β)) -
        pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g β) := by
    simp only [F, map_sub, actVB_mul, hcoc, map_add (f := _), LinearMap.add_apply,
      ← pairT_actVB (P.PD K) ρ ρ' m hD.1 g, hch]
    abel
  calc (ReciprocityTheory.Def.d1 (charRep (cycLL (P.PD K) ℚ_[l])) f (g, h)) ⊗ₜ[ℚ_[l]] (1 : P.R.B)
      = actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (f h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) -
          f (g * h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) + f g ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
        rw [hd1, tmul_one_sub_add, hact]
    _ = actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (F h) - F (g * h) + F g := by
        rw [hf h, hf (g * h), hf g]
    _ = _ := main
    _ = _ := hrhs.symm

theorem hyodo_orth : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → ∀ c ∈ geometricCocycles (P.PD K) ρ, ∀ a ∈ crystallineCocycles (P.PD K) ρ', CobL (P.PD K) (cupL ρ' m c a) := by
  intro l _ P AI hT K V _ _ _ _ _ _ _ ρ V' _ _ _ _ _ _ _ ρ' m hρ hρ' hdR hD c hc a ha
  by_cases hV : ∃ v : V, v ≠ 0
  · obtain ⟨v, hv⟩ := hV
    obtain ⟨v', hv'⟩ : ∃ v', m v v' ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (hD.2.1 v h)
    have hm : Continuous fun p : V × V' => m p.1 p.2 :=
      IsModuleTopology.continuous_bilinear_of_finite_left m
    have hχ : Continuous fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) := by
      have e : (fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])) =
          fun g => m (ρ g v) (ρ' g v') * (m v v')⁻¹ := by
        funext g
        rw [hD.1, mul_assoc, mul_inv_cancel₀ hv', mul_one]
      rw [e]
      exact (hm.comp ((hρ v).prodMk (hρ' v'))).mul continuous_const
    exact orth_of_cont l P AI hT K V ρ V' ρ' m hρ' hdR hD hχ c hc a ha
  · push_neg at hV
    refine ⟨0, continuous_const, funext fun x => ?_⟩
    simp [cupL, hV (c x.1), ReciprocityTheory.Def.d1]

end GlobalTheory.HyodoOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCrystallineOfLatticeReads
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.ReadPass

variable {l : ℕ} [Fact l.Prime]

theorem exists_read_map {Γ : Type} [Group Γ] {a d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l])
    (r : Γ →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l])
    (hR : Reads ρ r b e) (L : FinExt l) (r' : Γ →* GL (Fin a) ↥L.1)
    (R : Representation ↥L.1 Γ (Fin a → ↥L.1)) (hRr : ∀ g v, R g v = (r' g).val *ᵥ v)
    (hr : ∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (r g).val i j) (v : Fin a → ↥L.1) :
    ∃ (F : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : Fin d → ℚ_[l]),
      (∀ g y, F (qRep ρ g y) = R g (F y)) ∧ F x = v := by
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ↥L.1 (Om l))
    (LinearMap.ker_eq_bot.2 (algebraMap ↥L.1 (Om l)).injective)
  have hp' : ∀ c : ↥L.1, p (c : Om l) = c := fun c => LinearMap.congr_fun hp c
  let Φ : (Fin d → ℚ_[l]) → Matrix (Fin a) (Fin a) (Om l) := fun x => ∑ j, algebraMap ℚ_[l] (Om l) (x j) • b j
  let w : Fin a → Om l := fun k => (v k : Om l)
  have hΦs : ∀ (c : ℚ_[l]) x, Φ (c • x) = c • Φ x := by
    intro c x
    simp only [Φ, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, algebraMap_smul]
  have hΦa : ∀ x y, Φ (x + y) = Φ x + Φ y := by
    intro x y
    simp only [Φ, Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
  let F : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] (Fin a → ↥L.1) :=
    { toFun := fun x i => p ((Φ x *ᵥ w) i)
      map_add' := by
        intro x y; funext i
        simp only [hΦa, Matrix.add_mulVec, Pi.add_apply, map_add (f := _)]
      map_smul' := by
        intro c x; funext i
        have h1 : ((Φ (c • x)) *ᵥ w) i = c • ((Φ x *ᵥ w) i) := by
          rw [hΦs]
          simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, Matrix.smul_apply, smul_mul_assoc]
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [h1]
        exact LinearMap.map_smul_of_tower p c _ }
  have hq : ∀ g y, qRep ρ g y = ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ y := fun g y => rfl
  have hΦg : ∀ g y, Φ (qRep ρ g y) = (r g).val * Φ y := by
    intro g y
    rw [hq]
    simp only [Φ, Matrix.mul_sum, Matrix.mul_smul, hR.equi, Finset.smul_sum, smul_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  refine ⟨F, fun j => algebraMap ℤ_[l] ℚ_[l] (e j), fun g y => ?_, ?_⟩
  · funext i
    rw [hRr]
    change p ((Φ (qRep ρ g y) *ᵥ w) i) = ∑ k, (r' g).val i k * p ((Φ y *ᵥ w) k)
    rw [hΦg, ← Matrix.mulVec_mulVec]
    generalize Φ y *ᵥ w = z
    change p (∑ k, (r g).val i k * z k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hr]
    exact LinearMap.map_smul p ((r' g).val i k) (z k)
  · funext i
    change p ((Φ _ *ᵥ w) i) = v i
    have h1 : Φ (fun j => algebraMap ℤ_[l] ℚ_[l] (e j)) = 1 := hR.one
    rw [h1, Matrix.one_mulVec]
    exact hp' (v i)

end GlobalTheory.ReadPass

namespace GlobalTheory.ReadPass

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem crys_pass (T : LocTied l P AI) (K L : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] {a : ℕ} (ρq : Representation ℚ_[l] ↥(GK K) V)
    (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
    (hF : ∀ v : Fin a → ↥L.1, ∃ (F : V →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : V),
      (∀ g y, F (ρq g y) = R g (F y)) ∧ F x = v)
    (h : IsCrys (P.PD K) ρq) : IsCrys (P.PD K) R := by
  haveI := L.2
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have hf := GlobalTheory.TateDualCrys.fracInv_of_tied T K
  have hu := GlobalTheory.TateDualCrys.lineUnit_of_tied T K
  rw [GlobalTheory.RegularRing.isCrys_iff_span (P.PD K) hf hu] at h ⊢
  refine GlobalTheory.RegularRing.eq_top_of_tmul _ fun c v => ?_
  obtain ⟨F, x, hFe, rfl⟩ := hF v
  have hm : ∀ y ∈ DcrisK₀ (P.PD K) ρq, F.baseChange P.R.B y ∈ DcrisK₀ (P.PD K) R := by
    intro y hy
    rw [GlobalTheory.RegularRing.mem_DcrisK₀] at hy ⊢
    intro g
    have hc : ∀ z, F.baseChange P.R.B (GlobalTheory.RegularRing.sig (P.PD K) ρq g z) =
        GlobalTheory.RegularRing.sig (P.PD K) R g (F.baseChange P.R.B z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul b w => simp [GlobalTheory.RegularRing.sig_tmul, hFe]
      | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    rw [← hc, hy g]
  have h1 : Submodule.span P.R.B (DcrisK₀ (P.PD K) ρq : Set (P.R.B ⊗[ℚ_[l]] V)) ≤
      (Submodule.span P.R.B (DcrisK₀ (P.PD K) R : Set (P.R.B ⊗[ℚ_[l]] (Fin a → ↥L.1)))).comap
        (F.baseChange P.R.B) :=
    Submodule.span_le.2 fun y hy => Submodule.subset_span (hm y hy)
  have h2 := h1 (h ▸ Submodule.mem_top : c ⊗ₜ[ℚ_[l]] x ∈ _)
  simpa using h2

theorem dr_pass (T : LocTied l P AI) (K L : FinExt l) {LL0 : Type} [Field LL0] [Algebra ℚ_[l] LL0]
    {V : Type} [AddCommGroup V] [Module LL0 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL0 V] {a : ℕ}
    (ρ0 : Representation LL0 ↥(GK K) V) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
    (hF : ∀ v : Fin a → ↥L.1, ∃ (F : V →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : V),
      (∀ g y, F (ρ0 g y) = R g (F y)) ∧ F x = v)
    (h : GlobalTheory.DRFil.Spans (P.PD K) ρ0) : IsDR (P.PD K) R := by
  haveI := L.2
  apply GlobalTheory.DRFil.isDR_of_spans T K L R
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add y z hy hz =>
    obtain ⟨m, b, dd, hd, rfl⟩ := hy
    obtain ⟨m', b', dd', hd', rfl⟩ := hz
    refine ⟨m + m', Fin.append b b', Fin.append dd dd', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hd i
      · simpa using hd' i
    · rw [Fin.sum_univ_add]
      simp
  | tmul v c =>
    obtain ⟨F, x, hFe, rfl⟩ := hF v
    obtain ⟨m, b, dd, hd, hx⟩ := h (x ⊗ₜ[ℚ_[l]] c)
    let E : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR :=
      TensorProduct.map F (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR)
    have hE : ∀ (β : P.R.BdR) z, E (GlobalTheory.DRFil.mulR ℚ_[l] P.R.BdR LL0 V β z) =
        GlobalTheory.DRFil.mulR ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) β (E z) := by
      intro β z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul u c' => simp [E]
      | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    have hg : ∀ g z, E (actVdR (P.PD K) ρ0 g z) = actVdR (P.PD K) R g (E z) := by
      intro g z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul u c' => simp [E, actVdR, hFe]
      | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    refine ⟨m, b, fun i => E (dd i), fun i => ?_, ?_⟩
    · have h1 := hd i
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero] at h1 ⊢
      intro g
      rw [← hg, h1 g]
    · have h2 := congrArg E hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h2
      simp only [hE] at h2
      simpa [E] using h2

end GlobalTheory.ReadPass

namespace GlobalTheory.ReadPass

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem dr_pass_rat (T : LocTied l P AI) (K L : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] {a : ℕ} (ρq : Representation ℚ_[l] ↥(GK K) V)
    (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
    (hF : ∀ v : Fin a → ↥L.1, ∃ (F : V →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : V),
      (∀ g y, F (ρq g y) = R g (F y)) ∧ F x = v)
    (h : IsDR (P.PD K) ρq) : IsDR (P.PD K) R := by
  let LL : FinExt l := ⟨⊥, inferInstance⟩
  let e : (↥(LL.1)) ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI iM : Module (↥(LL.1)) V := Module.compHom V e.toRingEquiv.toRingHom
  haveI iT : IsScalarTower ℚ_[l] (↥(LL.1)) V :=
    ⟨fun q x v => by
      show e (q • x) • v = q • (e x • v)
      rw [show e (q • x) = q • e x from e.toLinearEquiv.map_smul q x, smul_eq_mul, mul_smul]⟩
  haveI iF : FiniteDimensional (↥(LL.1)) V := Module.Finite.of_restrictScalars_finite ℚ_[l] (↥(LL.1)) V
  let ρ' : Representation (↥(LL.1)) (↥(GK K)) V :=
    { toFun := fun g =>
        { toFun := ρq g, map_add' := (ρq g).map_add, map_smul' := fun x v => (ρq g).map_smul (e x) v }
      map_one' := by ext v; simp
      map_mul' := by intro g h; ext v; simp; rfl }
  have hact : ∀ g (x : V ⊗[ℚ_[l]] P.R.BdR), actVdR (P.PD K) ρ' g x = actVdR (P.PD K) ρq g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => rfl
    | add x z hx hz => rw [map_add (f := _), map_add (f := _), hx, hz]
  have hmem : ∀ x : V ⊗[ℚ_[l]] P.R.BdR, x ∈ DdR (P.PD K) ρ' ↔ x ∈ DdR (P.PD K) ρq := by
    intro x
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, hact]
  have hfr : ∀ (W : Type) [AddCommGroup W] [Module (↥(LL.1)) W] [Module ℚ_[l] W]
      [IsScalarTower ℚ_[l] (↥(LL.1)) W], Module.finrank (↥(LL.1)) W = Module.finrank ℚ_[l] W := by
    intro W _ _ _ _
    rw [← Module.finrank_mul_finrank ℚ_[l] (↥(LL.1)) W]
    have : Module.finrank ℚ_[l] (↥(LL.1)) = 1 := IntermediateField.finrank_bot
    rw [this, one_mul]
  let eq : ↥(DdR (P.PD K) ρ') ≃ₗ[ℚ_[l]] ↥(DdR (P.PD K) ρq) :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h' : IsDR (P.PD K) ρ' := by
    unfold IsDR at h ⊢
    rw [hfr, hfr, eq.finrank_eq, h]
  exact dr_pass T K L ρ' R hF ((GlobalTheory.DRFil.filSpans T K LL ρ' h').spans)

theorem isDR_isCrys_of_reads : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (r : ↥(GK K) →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (r g).val i j) → (Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) → Formalism.MainNotions.N.IsDR (P.PD K) R) ∧ (IsCrys (P.PD K) (qRep ρ) → IsCrys (P.PD K) R) := by
  intro l _ K L₀ P AI T a d ρ r b e hR L r' R _ hRr hr
  have hF := exists_read_map ρ r b e hR L r' R hRr hr
  exact ⟨dr_pass_rat T K L (qRep ρ) R hF, crys_pass T K L (qRep ρ) R hF⟩

end GlobalTheory.ReadPass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlochKatoCocycleOfCrysDeRhamPairStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blochKato_cocycle_of_crys_deRham_pair : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, ∀ d₁ ∈ Dcris (P.PD K) A.ρ, ∀ d₂ ∈ DdR (P.PD K) A.ρ, ∃ (x : A.V ⊗[ℚ_[l]] P.R.B) (y : A.V ⊗[ℚ_[l]] P.R.BdR) (c : ↥(GK K) → A.V), y ∈ FilV (P.PD K) (LL := LL) (V := A.V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := A.V) x = d₁ ∧ ιV (P.PD K) (LL := LL) (V := A.V) x - y = d₂ ∧ c ∈ finiteCocycles (P.PD K) A.ρ ∧ ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x := by
  first | exact @GlobalTheory.FundDel.connecting_cocycle | exact GlobalTheory.FundDel.connecting_cocycle | (intros; apply GlobalTheory.FundDel.connecting_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedPeriodsDiscAinfStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bounded_periods_disc_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∃ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (k : ℕ) (v : ι → Matrix (Fin d) (Fin d) (Ainf l)) (Z : ι → Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (∀ (n : ℕ) (a b : Fin d), {i | v i a b ∉ (bk.J ^ n).map bk.ev}.Finite) ∧ (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ i, s.W * (Z i).map j = (v i).map bk.iA) ∧ ∀ a b : Fin d, HasSum (fun i => bk.iA (v i a b * TB.b i)) (bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0)) := by
  first | exact @GlobalTheory.BSP.exists_bounded_periods | exact GlobalTheory.BSP.exists_bounded_periods | (intros; apply GlobalTheory.BSP.exists_bounded_periods <;> assumption)
end

