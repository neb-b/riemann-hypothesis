module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField Filter
open IsDedekindDomain
open scoped TensorProduct RestrictedProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPl.SplitPoint

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke

open Classical in
theorem continuous_single_at (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem continuous_eval_at (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v

theorem mem_integer_iff (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) :
    a ∈ 𝒪[Fv F v] ↔ a ∈ v.adicCompletionIntegers F := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation (Fv F v)), ← Valuation.Compatible.vle_iff_le,
    HeightOneSpectrum.mem_adicCompletionIntegers,
    ← map_one (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))]
  exact Iff.rfl

variable {D : D7} {v : Pl D} {e : AE D}

theorem splitAt_of {ε : AF D.host.F} (h : IsSplitIdem D e) (hε : IsPlaceIdem D v ε)
    (he : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SplitAt D v e := by
  obtain ⟨α, rfl, h3, h4⟩ := hε
  have : α = singleV D.host.F v 1 := af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h3, evalV_singleV_same]
    · rw [h4 w hw, evalV_singleV_ne _ v _ hw]
  subst this
  exact ⟨h.1, h.2.1, he⟩

def sec (D : D7) (v : Pl D) (e : AE D) : Fv D.host.F v →+ AE D :=
  AddMonoidHom.ofMapSub (fun a => fj D (singleV D.host.F v a) * e) fun x y => by
    rw [singleV_sub, map_sub, sub_mul]

theorem sec_apply (a : Fv D.host.F v) : sec D v e a = fj D (singleV D.host.F v a) * e := rfl

theorem continuous_sec : Continuous (sec D v e) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h1 : Continuous fun x : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v x) :=
    Continuous.prodMk continuous_const (continuous_single_at _ v)
  have h2 : Continuous (algebraMap (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))
  exact (h2.comp h1).mul continuous_const

theorem continuous_comp (he : SplitAt D v e) : Continuous (comp he) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  let σ : AF D.host.F →+* Fv D.host.F v := ((evalV D.host.F v).comp (sndA D.host.F)).toRingHom
  have hσ : Continuous σ := (continuous_eval_at _ v).comp continuous_snd
  let L : AE D →ₛₗ[σ] Fv D.host.F v :=
    { toFun := comp he
      map_add' := map_add _
      map_smul' := fun a x => by
        rw [Algebra.smul_def, map_mul, comp_algebraMap]
        rfl }
  exact IsModuleTopology.continuous_of_linearMapₛₗ hσ L

theorem exists_splitPt : ∀ (D : D7) (v : Pl D) (e : AE D) (ε : AF D.host.F), IsSplitIdem D e → IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → ∃ p : SplitPt D (Fv D.host.F v), p.e = e ∧ p.v = v := by
  intro D v e ε h hε hs
  have he : SplitAt D v e := splitAt_of h hε hs
  have hps : ∀ a, comp he (sec D v e a) = a := fun a => by
    rw [sec_apply, map_mul, comp_fj, comp_self, mul_one, evalV_singleV_same]
  have hsp : ∀ x, sec D v e (comp he x) = e * x := fun x => (sc_spec he x).symm
  refine ⟨{
    v := v
    e := e
    split := h
    above := ⟨ε, hε, hs⟩
    pr := comp he
    sec := sec D v e
    pr_sec := hps
    sec_pr := hsp
    cont_pr := continuous_comp he
    cont_sec := continuous_sec
    int_iff := fun a => ?_ }, rfl, rfl⟩
  have h1 := (chart_comp he).2.2.2 (sec D v e a)
  rw [← hsp, hps] at h1
  rw [h1, isInt_Ov, mem_integer_iff]

end GlobalTheory.FinPl.SplitPoint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FrameCont
open Matrix

theorem gram_det_isUnit {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) :
    IsUnit S.gram.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ v : Fin S.rank → E, S.gram *ᵥ v = 0 → v = 0 := by
    intro v hv
    have h0 : ∑ j, v j • S.frame j = 0 := by
      apply S.nondeg.2
      intro x
      rw [← S.frame.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at hi
      calc _ = (starRingEnd E) (S.frame.repr x i) * ∑ j, S.hT (S.frame i) (S.frame j) * v j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hi, mul_zero]
    funext j
    exact Fintype.linearIndependent_iff.1 S.frame.linearIndependent v h0 j
  intro a b hab
  have := key (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self])
  exact sub_eq_zero.1 this

theorem continuous_of_parts {A T m : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace T] [Fintype m] [DecidableEq m] (σ : A →+* A) (hσ : Continuous σ) (e : A)
    (J : Matrix m m A) (hJ : IsUnit J.det) (M N : T → Matrix m m A)
    (hU : ∀ t, Formalism.UG.cT σ (N t) * J * N t = J) (hNM : ∀ t, N t * M t = 1)
    (hs : ∀ t i j, (e + σ e) * (M t - 1) i j = (M t - 1) i j)
    (hM : Continuous fun t => e • M t) (hN : Continuous fun t => e • N t) : Continuous M := by
  have hc : ∀ t, σ e • M t = J⁻¹ * Formalism.UG.cT σ (e • N t) * J := by
    intro t
    have h1 : J * M t = Formalism.UG.cT σ (N t) * J := by
      calc J * M t = Formalism.UG.cT σ (N t) * J * N t * M t := by rw [hU]
        _ = Formalism.UG.cT σ (N t) * J := by rw [Matrix.mul_assoc _ (N t) (M t), hNM, Matrix.mul_one]
    have h2 : Formalism.UG.cT σ (e • N t) = σ e • Formalism.UG.cT σ (N t) := by
      ext a b; simp [Formalism.UG.cT]
    rw [h2, Matrix.mul_assoc, Matrix.smul_mul, ← h1, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]
  have hC : Continuous fun t => σ e • M t := by
    simp only [hc]
    exact (continuous_const.matrix_mul (hN.matrix_map hσ).matrix_transpose).matrix_mul continuous_const
  have hsum : M = fun t => (1 - (e + σ e) • (1 : Matrix m m A)) + (e • M t + σ e • M t) := by
    funext t
    ext i j
    have h := hs t i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢
    linear_combination -h
  rw [hsum]
  exact continuous_const.add (hM.add hC)

theorem continuous_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  have h := IsModuleTopology.continuous_of_linearMap (R := R) (LinearMap.baseChange R σ.toLinearMap)
  refine h.congr fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [LinearMap.baseChange_tmul, sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem unitary_mt {D : D7} {S : HSp D} (x : GA D S) :
    Formalism.UG.cT (cA D) (mt S x) * S.gram.map (incA D) * mt S x = S.gram.map (incA D) := (PI.FT.toHR x).2

theorem mt_inv_mul {D : D7} {S : HSp D} (x : GA D S) : mt S x⁻¹ * mt S x = 1 := by
  show (matHom S x⁻¹).val * (matHom S x).val = 1
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem gram_map_det_isUnit {D : D7} (S : HSp D) : IsUnit (S.gram.map (incA D)).det := by
  have h0 := (gram_det_isUnit S).map (incA D)
  rw [RingHom.map_det] at h0
  exact h0

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem e_mul_entry (β : Frame p S n) (g : GL n k) (i j : Fin S.rank) :
    p.e * mt S (β.gl g) i j = p.sec ((β.b * g.val * β.b') i j) := by
  rw [← p.sec_pr, ← β.gl_mat g]; rfl

theorem continuous_e_smul (β : Frame p S n) : Continuous fun g : GL n k => p.e • mt S (β.gl g) := by
  refine continuous_matrix fun i j => ?_
  refine (p.cont_sec.comp (((continuous_const.matrix_mul
    (Units.continuous_val (M := Matrix n n k))).matrix_mul continuous_const).matrix_elem i j)).congr
      fun g => (e_mul_entry β g i j).symm

theorem continuous_mt (β : Frame p S n) : Continuous fun g : GL n k => mt S (β.gl g) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  refine continuous_of_parts (cA D) (continuous_sigR _ _) p.e (S.gram.map (incA D)) (gram_map_det_isUnit S)
    (fun g => mt S (β.gl g)) (fun g => mt S (β.gl g⁻¹)) (fun g => unitary_mt _) (fun g => ?_)
    (fun g => β.gl_supp g) (continuous_e_smul β) ((continuous_e_smul β).comp continuous_inv)
  show mt S (β.gl g⁻¹) * mt S (β.gl g) = 1
  rw [map_inv]
  exact mt_inv_mul _

theorem continuous_gl : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), Continuous β.gl := by
  intro D k _ _ _ _ p S n _ _ β
  refine (PI.FT.cont_HA_iff (AF D.host.F) (fun g : GL n k => β.gl g)).2 ⟨continuous_mt β, ?_⟩
  have h := (continuous_mt β).comp (continuous_inv (G := GL n k))
  refine h.congr fun g => ?_
  show mt S (β.gl g⁻¹) = PI.FT.mtI (β.gl g)
  rw [map_inv]; rfl

end GlobalTheory.FrameCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvalVIndP
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField

namespace GlobalTheory.VacLoc

variable {D : D7}

open scoped Classical

def indP (D : D7) (X : Set (Pl D)) : Af D.host.F :=
  ⟨fun v => if v ∈ X then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ X <;> simp [h, one_mem, zero_mem]⟩

theorem evalV_indP (X : Set (Pl D)) (v : Pl D) :
    evalV D.host.F v (indP D X) = if v ∈ X then 1 else 0 := rfl

theorem indicatorAdele_mem_integralAdeles (X : Set (Pl D)) : indP D X ∈ intAf D.host.F := by
  intro v; rw [evalV_indP]; by_cases h : v ∈ X <;> simp [h, one_mem, zero_mem]

theorem finiteAdele_ext {a b : Af D.host.F} (h : ∀ v, evalV D.host.F v a = evalV D.host.F v b) : a = b :=
  RestrictedProduct.ext _ _ h

theorem indicatorAdele_singleton_mul_singleton (X Y : Set (Pl D)) : indP D X * indP D Y = indP D (X ∩ Y) := by
  apply finiteAdele_ext; intro v; rw [map_mul, evalV_indP, evalV_indP, evalV_indP]
  by_cases hX : v ∈ X <;> by_cases hY : v ∈ Y <;> simp [hX, hY]

theorem indicatorAdele_union_of_disjoint {X Y : Set (Pl D)} (h : Disjoint X Y) : indP D X + indP D Y = indP D (X ∪ Y) := by
  apply finiteAdele_ext; intro v; rw [map_add (f := _), evalV_indP, evalV_indP, evalV_indP]
  by_cases hX : v ∈ X <;> by_cases hY : v ∈ Y <;> simp [hX, hY]
  exact Set.disjoint_left.mp h hX hY

theorem indicatorAdele_univ : indP D Set.univ = 1 := by
  apply finiteAdele_ext; intro v; rw [evalV_indP, map_one]; simp

theorem indicatorAdele_empty : indP D ∅ = 0 := by
  apply finiteAdele_ext; intro v; rw [evalV_indP, map_zero]; simp

end GlobalTheory.VacLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyExtUnramTwoNotMem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem eventually_extUnram_two_notMem : ∀ D : D7, ∀ᶠ v : Pl D in cofinite, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v ∧ (2 : 𝓞 D.host.F) ∉ v.asIdeal := by
  intro D
  rw [Filter.eventually_cofinite]
  have h2 : (2 : 𝓞 D.host.F) ≠ 0 := two_ne_zero
  have hB : (Ideal.span {(2 : 𝓞 D.host.F)}) ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using h2
  have hfin2 := Ideal.finite_factors hB
  have hfinD := Ideal.finite_factors
    (differentIdeal_ne_bot (A := 𝓞 D.host.F) (B := 𝓞 D.host.E))
  have hfinU : ((fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.asIdeal.under (𝓞 D.host.F)) ''
      {Q | Q.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E)}).Finite := hfinD.image _
  have hfinA : {v : Pl D | v.asIdeal ∈ (fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.asIdeal.under (𝓞 D.host.F)) ''
      {Q | Q.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E)}}.Finite :=
    hfinU.preimage (f := fun v : Pl D => v.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
  refine (hfinA.union hfin2).subset fun v hv => ?_
  by_cases h : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · right
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h)
  · left
    have hE : ¬ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v := fun hu => hv ⟨hu, h⟩
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt at hE
    push_neg at hE
    obtain ⟨P, hP, hL, hU⟩ := hE
    have hover : v.asIdeal = P.under (𝓞 D.host.F) := hL.over
    have hPb : P ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [hover, Ideal.under_bot]
    refine ⟨⟨P, hP, hPb⟩, ?_, hover.symm⟩
    by_contra hd
    exact hU (not_dvd_differentIdeal_iff.1 hd)

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
open IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.AeUnit

theorem idem_mul_finPart (D : D7) (v : Pl D) {a : AE D} (ha : a ∈ idAt D (· = v)) :
    (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a = finPart D a := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_
  rw [map_mul, Algebra.TensorProduct.map_tmul]
  by_cases hw : w = v
  · subst hw
    rw [GlobalTheory.LatVac.evalV_singleV_same, map_one, ← Algebra.TensorProduct.one_def, one_mul]
  · have h0 : GlobalTheory.FinPl.compAt D w a = 0 := (Submodule.mem_iInf _).1 ha.2 ⟨w, hw⟩
    have h1 : Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E) (finPart D a) = 0 := h0
    rw [h1, mul_zero]

theorem inv_smul_singleV_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℤ)
    (h : (N : 𝓞 F) ∉ v.asIdeal) : (N : F)⁻¹ • singleV F v 1 ∈ intAf F := by
  intro w
  rw [map_smul]
  by_cases hw : w = v
  · subst hw
    rw [GlobalTheory.LatVac.evalV_singleV_same, ← Algebra.algebraMap_eq_smul_one,
      HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : w.valuation F (algebraMap (𝓞 F) F N) = 1 := (w.valuation_eq_one_iff_notMem (K := F)).2 h
    rw [map_intCast] at h1
    have h2 : Valued.v (algebraMap F (Fv F w) (N : F)⁻¹) = w.valuation F (N : F)⁻¹ :=
      w.valuedAdicCompletion_eq_valuation' _
    rw [h2, map_inv₀, h1, inv_one]
  · rw [GlobalTheory.LatVac.evalV_singleV_ne F v w hw, smul_zero]
    exact zero_mem _

theorem tmul_eq_inv_smul_tmul {F M P : Type} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup P] [Module F P]
    (N : ℤ) (hN : (N : F) ≠ 0) (x : M) (c : P) : x ⊗ₜ[F] c = ((N : F)⁻¹ • x) ⊗ₜ[F] (N • c) := by
  rw [TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul F N c, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem eventually_incA_mul_mem_intAt : ∀ (D : D7) (c : D.host.E), ∀ᶠ v : Pl D in cofinite,
    ∀ a ∈ intAt D (· = v), incA D c * a ∈ intAt D (· = v) := by
  intro D c
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨N, hN, hint⟩ := halg.exists_integral_multiple
  have hN' : (N : 𝓞 D.host.F) ≠ 0 := Int.cast_ne_zero.2 hN
  have hNF : (N : D.host.F) ≠ 0 := Int.cast_ne_zero.2 hN
  have hfin := Ideal.finite_factors (I := Ideal.span {(N : 𝓞 D.host.F)})
    (fun h => hN' (Ideal.span_singleton_eq_bot.1 h))
  filter_upwards [hfin.compl_mem_cofinite] with v hv a ha
  have hv' : (N : 𝓞 D.host.F) ∉ v.asIdeal := fun h => hv (Ideal.dvd_span_singleton.2 h)
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, inv_smul_singleV_mem v N hv', ⟨N • c, hint⟩, ?_⟩
  exact tmul_eq_inv_smul_tmul N hNF _ c

end GlobalTheory.FinPl.AeUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicTraceCharacterSplitSectionNeOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
open IsDedekindDomain

namespace GlobalTheory.FinPl.CharNontriv

theorem exists_psiV_ne_one (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ y, ψ (pairA D.host.F 0 (singleV D.host.F v y)) ≠ 1 := by
  have h := hψ.1
  have h' : IsCharAF D.host.F ψ⁻¹ := by
    refine ⟨h.1.comp continuous_neg, fun x => h.2.1 _, fun a => ?_, ?_⟩
    · rw [AddChar.inv_apply, ← map_neg]; exact h.2.2.1 _
    · obtain ⟨x, hx⟩ := h.2.2.2
      exact ⟨-x, by rwa [AddChar.inv_apply, neg_neg]⟩
  obtain ⟨y, hy⟩ := GlobalTheory.StdCharTotReal.psiV_ne_one_of_trace h' (fun a => by
    rw [← GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, GlobalTheory.StdRat.char_fin_rat ψ h, psiInf, psiInf, AddChar.inv_apply,
      map_neg (algebraMap D.host.F (Ainf D.host.F))]
    refine congrArg ψ (Prod.ext rfl ?_)
    exact neg_zero) v
  refine ⟨y, fun h1 => hy ?_⟩
  rw [psiV, AddChar.inv_apply', h1, inv_one]

theorem algebraMap_injective (D : D7) : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective

theorem exists_psiE_sec_ne_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ a : k, GlobalTheory.MixPer.psiE ψ (p.sec a) ≠ 1 := by
  intro D k _ _ _ _ p ψ hψ
  obtain ⟨y, hy⟩ := exists_psiV_ne_one D ψ hψ p.v
  obtain ⟨ε, ⟨α, rfl, h1, -⟩, he⟩ := p.above
  have ht : Algebra.trace (AF D.host.F) (AE D) p.e = pairA D.host.F 0 α :=
    algebraMap_injective D ((GlobalTheory.FockCompare.SymplVal.trace_AE D p.e).trans he)
  refine ⟨p.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F p.v y))), ?_⟩
  rw [p.sec_pr, GlobalTheory.MixPer.psiE, mul_comm, ← Algebra.smul_def, map_smul, ht, smul_eq_mul]
  have h2 : pairA D.host.F 0 (singleV D.host.F p.v y) * pairA D.host.F 0 α =
      pairA D.host.F 0 (singleV D.host.F p.v y) := by
    refine Prod.ext (zero_mul _) ?_
    show singleV D.host.F p.v y * α = singleV D.host.F p.v y
    have h3 : α p.v = 1 := h1
    rw [GlobalTheory.StdCharTotReal.single_mul, h3, mul_one]
  rwa [h2]

end GlobalTheory.FinPl.CharNontriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiKernelEqWeilRepresentationApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem fjKer_eq_om_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W W₀ V₀ A L : HSp D) (ρ : ℕ) (dW : HypDec W W₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om V₀ W₀), IsWeilDatumO ψ V₀ W₀ χ χ' om → ∀ Ξ, IsThetaFunO ψ V₀ W₀ Ξ → ∀ h₀ n h, fjKer ψ dW o ζ om Ξ h₀ n h = ψ (cenT dW L (yZero L ρ ζ) n) * om (o.emb (h₀, 1), h) Ξ ((o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n)) := by
  intro D ψ W W₀ V₀ A L ρ dW o ζ χ χ' om hW Ξ hΞ h₀ n h
  have hp : (o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n) = ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n := by
    rw [← ptT_yZero_vecB o dW ζ n, AddEquiv.symm_apply_apply]
  have hfix : actO V₀ W₀ (o.emb (h₀, 1)) 1 (ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n) =
      ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n := by
    apply (o.resS W₀).injective
    rw [o.resS_actO, ptT_yZero_vecB]
    simp only [actO_eq, inv_one, mt_one, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul]
  have hm : om (o.emb (h₀, 1), 1) (om (1, h) Ξ) = om (o.emb (h₀, 1), h) Ξ := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [hp, fjKer, opA, jacT, map_smul, hW.om_heis _ _ _ _ (hW.om_pres _ _ hΞ), hfix, hm, cenT_yZero_vecB]
  simp only [Pi.smul_apply, smul_eq_mul, heisO, zero_add, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.Unf
end

