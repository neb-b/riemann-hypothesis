module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalArchimedeanFactor
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitIdelesOpen
section
noncomputable section

namespace GlobalTheory.ThK.ConeEuler.UnitsOpen

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

section Lemmas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isOpen_integral_everywhere : IsOpen {z : AE F E | ∀ v : Pl F, compFin F E v z ∈ intLoc F E v} := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  let S : AddSubgroup (AE F E) :=
    { carrier := {z | ∀ v : Pl F, compFin F E v z ∈ intLoc F E v}
      zero_mem' := fun v => by rw [map_zero]; exact zero_mem _
      add_mem' := fun ha hb v => by rw [map_add]; exact add_mem (ha v) (hb v)
      neg_mem' := fun ha v => by rw [map_neg]; exact neg_mem (ha v) }
  let b := integralBasis E
  let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → AF F) →ₗ[AF F] AE F E :=
    Fintype.linearCombination (AF F) fun i => (1 : AF F) ⊗ₜ[F] b i
  have hφ : ∀ a, φ a = ∑ i, a i ⊗ₜ[F] b i := fun a => by
    simp only [φ, Fintype.linearCombination_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hq : ∀ (c : ℚ) (a : AF F) (x : E), a ⊗ₜ[F] (c • x) = (algebraMap F (AF F) (c : F) * a) ⊗ₜ[F] x := fun c a x => by
    rw [show c • x = (c : F) • x by rw [Rat.cast_smul_eq_qsmul], ← TensorProduct.smul_tmul, Algebra.smul_def]
  have hsurj : Function.Surjective φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a x =>
      refine ⟨fun i => algebraMap F (AF F) (b.repr x i : F) * a, ?_⟩
      rw [hφ]
      conv_rhs => rw [← b.sum_repr x, TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun i _ => (hq _ _ _).symm
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hy
      exact ⟨a + c, map_add _ _ _⟩
  let W : Set (AF F) := {a | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  have ho : IsOpen W :=
    (RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 F) =>
      Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage continuous_snd
  have hopen : IsOpen (φ '' Set.univ.pi fun _ => W) :=
    (IsModuleTopology.isOpenQuotientMap_of_surjective hsurj).isOpenMap _
      (isOpen_set_pi Set.finite_univ fun _ _ => ho)
  have hsub : φ '' (Set.univ.pi fun _ => W) ⊆ (S : Set (AE F E)) := by
    rintro _ ⟨a, ha, rfl⟩ v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ, map_sum]
    refine sum_mem fun i _ => ?_
    rw [show b i = ((RingOfIntegers.basis E i : 𝓞 E) : E) from integralBasis_apply E i]
    exact tmul_mem_intLoc (ha i (Set.mem_univ i) v) _
  have h0 : (0 : AE F E) ∈ φ '' (Set.univ.pi fun _ => W) :=
    ⟨0, fun i _ v => by simp, map_zero φ⟩
  exact (AddSubgroup.isOpen_of_mem_nhds S (g := 0) (Filter.mem_of_superset (hopen.mem_nhds h0) hsub) :
    IsOpen (S : Set (AE F E)))

end Lemmas

end GlobalTheory.ThK.ConeEuler.UnitsOpen

namespace GlobalTheory.ThK.ConeEuler

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

end GlobalTheory.ThK.ConeEuler
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFinitePartIdempotentBlendMemLatticeStabil
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.StabMove

theorem mul_entries_mem {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) (hN : ∀ i j, N i j ∈ R) :
    ∀ i j, (M * N) i j ∈ R := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem R fun k _ => R.mul_mem (hM i k) (hN k j)

def lift {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) : Matrix (Fin n) (Fin n) R :=
  fun i j => ⟨M i j, hM i j⟩

theorem lift_map {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) :
    (lift R M hM).map R.subtype = M := by
  ext i j; rfl

def liftGL {A : Type} [CommRing A] (R : Subring A) {n : ℕ} (u : GL (Fin n) A)
    (hu : ∀ i j, u.val i j ∈ R) (hu' : ∀ i j, (u⁻¹).val i j ∈ R) : GL (Fin n) R where
  val := lift R u.val hu
  inv := lift R (u⁻¹).val hu'
  val_inv := by
    apply Matrix.map_injective (f := R.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul (f := R.subtype), lift_map, lift_map, Matrix.map_one _ (map_zero _) (map_one _)]
    exact u.mul_inv
  inv_val := by
    apply Matrix.map_injective (f := R.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul (f := R.subtype), lift_map, lift_map, Matrix.map_one _ (map_zero _) (map_one _)]
    exact u.inv_mul

theorem liftGL_map {A : Type} [CommRing A] (R : Subring A) {n : ℕ} (u : GL (Fin n) A)
    (hu : ∀ i j, u.val i j ∈ R) (hu' : ∀ i j, (u⁻¹).val i j ∈ R) :
    Formalism.UG.bc R.subtype (liftGL R u hu hu') = u := by
  ext i j; rfl

end GlobalTheory.StabMove

open GlobalTheory.StabMove in
theorem GlobalTheory.StabMove.finE_mem_St : ∀ {D : D7} (V : HSp D) (g : GA D V) (β₀ β₁ : GL (Fin V.rank) (Lev.EAf D)),
    (∀ i j, β₀.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₀⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, β₁.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₁⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∀ ε φ : Lev.EAf D, ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → φ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₁ * β₀⁻¹).val + φ • ((β₀ * β₁⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₀ * β₁⁻¹).val + φ • ((β₁ * β₀⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β₁ := by
  intro D V g β₀ β₁ h₀ h₁ ε φ hε hφ hg hg'
  set R := Formalism.L2.Herm.intAf D.host.F D.host.E with hR
  have hcF : ∀ M : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D), (∀ i j, M i j ∈ R) →
      ∀ i j, ((M.map (GlobalTheory.AdelicLatMove.cF D)).transpose) i j ∈ R := by
    intro M hM i j
    exact GlobalTheory.LevSplit.sigR_int (hM j i)
  have hshape : ∀ (a b : GL (Fin V.rank) (Lev.EAf D)), (∀ i j, a.val i j ∈ R ∧ (a⁻¹).val i j ∈ R) →
      (∀ i j, b.val i j ∈ R ∧ (b⁻¹).val i j ∈ R) →
      ∀ i j, ((1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
        ε • (a * b⁻¹).val + φ • ((b * a⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose) i j ∈ R := by
    intro a b ha hb i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine R.add_mem (R.add_mem (R.mul_mem ?_ ?_) (R.mul_mem hε ?_)) (R.mul_mem hφ ?_)
    · exact R.sub_mem (R.sub_mem R.one_mem hε) hφ
    · rw [Matrix.one_apply]; split_ifs
      · exact R.one_mem
      · exact R.zero_mem
    · rw [Units.val_mul]
      exact mul_entries_mem R _ _ (fun i j => (ha i j).1) (fun i j => (hb i j).2) i j
    · apply hcF
      rw [Units.val_mul]
      exact mul_entries_mem R _ _ (fun i j => (hb i j).1) (fun i j => (ha i j).2)
  have hE : ∀ i j, (Formalism.IndefR.Lev.finE V g).val i j ∈ R := by
    have : (Formalism.IndefR.Lev.finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := rfl
    rw [this, hg]; exact hshape β₁ β₀ h₁ h₀
  have hE' : ∀ i j, ((Formalism.IndefR.Lev.finE V g)⁻¹).val i j ∈ R := by
    have : ((Formalism.IndefR.Lev.finE V g)⁻¹).val = (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) := by
      rw [← map_inv]; rfl
    rw [this, hg']; exact hshape β₀ β₁ h₀ h₁
  set u := β₁⁻¹ * Formalism.IndefR.Lev.finE V g * β₁ with hu
  have hu1 : ∀ i j, u.val i j ∈ R := by
    intro i j
    simp only [hu, Units.val_mul]
    exact mul_entries_mem R _ _ (mul_entries_mem R _ _ (fun i j => (h₁ i j).2) hE) (fun i j => (h₁ i j).1) i j
  have hu2 : ∀ i j, (u⁻¹).val i j ∈ R := by
    intro i j
    have : u⁻¹ = β₁⁻¹ * (Formalism.IndefR.Lev.finE V g)⁻¹ * β₁ := by
      simp only [hu, mul_inv_rev, inv_inv, mul_assoc]
    rw [this]
    simp only [Units.val_mul]
    exact mul_entries_mem R _ _ (mul_entries_mem R _ _ (fun i j => (h₁ i j).2) hE') (fun i j => (h₁ i j).1) i j
  refine ⟨liftGL R u hu1 hu2, ?_⟩
  show MulAut.conj β₁ (Formalism.UG.bc R.subtype (liftGL R u hu1 hu2)) = _
  rw [liftGL_map, MulAut.conj_apply, hu]
  group
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveGoodModel
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ModelAdmUnconditional

open Filter
open scoped Classical

theorem model_admissible_iff_evaluation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ l : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) ↔ l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij l
  constructor
  · intro hl
    exact GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE l hl
  · intro hl g hg
    obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg
    obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
    have hbi : Function.Bijective ei :=
      ⟨GlobalTheory.T.weil_eigen_injective_extends F E σ B n d X W M M₁ hP.good e hbij.injOn ei ev (fun v => (hev v).1) hloc,
        GlobalTheory.T.weil_eigen_surjective_extends F E σ B n d X W M M₁ hP.good hM₁ e hbij.surjOn ei ev hev hloc⟩
    obtain ⟨S, hS⟩ := _root_.GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse _ _ ei hbi
    have hpre : ∀ j v, ∃ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ = φ j v ∧ (φ j v = M₁.vac v → ψ = M.vac v) := by
      intro j v
      by_cases h : φ j v = M₁.vac v
      · exact ⟨M.vac v, (hP.good.vac v).1, (hev v).1.trans h.symm, fun _ => rfl⟩
      · have h2 : φ j v ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v) := (hev v).2.symm ▸ hφ j v
        obtain ⟨ψ, hψ, hψe⟩ := Submodule.mem_map.1 h2
        exact ⟨ψ, hψ, hψe, fun h' => (h h').elim⟩
    choose ψ hψSB hψev hψvac using hpre
    have hψfam : ∀ j, ∀ᶠ v in cofinite, ψ j v = M.vac v := fun j =>
      ((hstd j).and hM₁.std).mono fun v hv => hψvac j v (hv.1.trans hv.2.symm)
    have hψstd : ∀ j, ∀ᶠ v in cofinite,
        ψ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
      ((hψfam j).and hP.good.std).mono fun v hv => hv.1.trans hv.2
    have hG : ∀ j, (fun y : Fin n × Fin d → Af F => ∏ᶠ v, ψ j v fun i => evalV F v (y i)) ∈
        SB (Fin n × Fin d → Af F) := fun j =>
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
        GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
    choose Tj hTj using fun j => hl _ (hG j)
    refine ⟨∑ j, c j • (Tj j).comp S, fun f => ?_⟩
    have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
        (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
        ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
      funext x
      simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm]
      rfl
    have hφe : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) =
        e (pureA F ((S f : SInf F _) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
          (fun y => ∏ᶠ v, ψ j v fun i => evalV F v (y i))) := by
      intro j
      have h1 := hloc (S f) (ψ j) (hψSB j) (hψfam j)
      rw [hS] at h1
      have h2 : (fun v => ev v (ψ j v)) = φ j := funext fun v => hψev j v
      rw [h2] at h1
      exact h1.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsplit, map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hφe j]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [← hTj j (S f)]
    rfl

end GlobalTheory.ModelAdmUnconditional
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSchwartzSurjective
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section
namespace GlobalTheory.ThetaChange

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c₀ * thetaSum F Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij
  have hstd : IsStd B.ψ := hP.base.std
  have hrk : Module.finrank F E = 2 := hP.base.cm.2.2.1
  obtain ⟨Φr, hΦr⟩ := GlobalTheory.RatCoord.ratEquiv F E σ n d X W M B.ψ hP.good hrk
  obtain ⟨lθ, hlθ, hlθ'⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  have hcomp := GlobalTheory.EvAdm.comp_mem_adm F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE lθ hlθ
  have hinc1 : ∀ k : ℕ, incM F (1 : Matrix (Fin k) (Fin k) E) = 1 := by
    intro k; unfold incM; exact Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.ThetaFunctionalUnique.main F B.ψ hstd (Fin n × Fin d) (fun Φ => thetaSum F (e Φ))
    (fun Φ hΦ Ψ hΨ => by
      simp only [map_add (f := _)]
      exact GlobalTheory.WeilM.thetaSum_add F (hE.maps Φ hΦ) (hE.maps Ψ hΨ))
    (fun c Φ _ => by simp only [map_smul]; exact GlobalTheory.WeilM.thetaSum_smul F c (e Φ))
    (fun g hg => by
      obtain ⟨T, hT⟩ := hcomp g hg
      refine ⟨T, fun f => ?_⟩
      have hm : pureA F f g ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
      rw [← hlθ' _ (hE.maps _ hm)]
      exact hT f)
    (fun a b Φ hΦ => by
      set x := Φr.symm (a, b) with hx
      have hxe : M.co.e (incM F x) = ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) := by
        rw [hΦr x, hx, LinearEquiv.apply_symm_apply]
      have h1 : schr B.ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ =
          M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * incM F x * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ := by
        rw [hinc1, hinc1, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
        show _ = schr B.ψ (M.co.e (incM F x)) Φ
        rw [hxe]
      rw [h1, hE.Heisenberg₂ _ Φ hΦ]
      obtain ⟨y, z, hyz⟩ := hM₁.rat x
      show thetaSum F (schr B.ψ (M₁.co.e (incM F x)) (e Φ)) = _
      rw [hyz]
      exact GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ (fun a => hstd.2.1 a) y z (e Φ))
  refine ⟨c, ?_, hc⟩
  rintro rfl
  obtain ⟨φ₀, hφ₀, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin n × Fin d)
  obtain ⟨Φ, hΦ, rfl⟩ := hbij.surjOn hφ₀
  exact hne (by rw [hc Φ hΦ, zero_mul])

end GlobalTheory.ThetaChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaFunctionTransportLocalFieldIso
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

section
variable {k k' : Type} [Field k] [Field k'] {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem gdet_glTrEquiv_ffun (j : k ≃+* k') (e : D₂ ≃ D) (g : GL D k) :
    gdet (glTrEquiv j e g) = Units.map (j : k →* k') (gdet g) := by
  apply Units.ext
  show (glTrEquiv j e g).val.det = j g.val.det
  rw [glTrEquiv_val, show trM j e e g.val = (g.val.map j).submatrix e e from rfl, det_submatrix_equiv_self]
  exact ((j : k →+* k').map_det g.val).symm

theorem invT_glTrEquiv_ffun (j : k ≃+* k') (e : D₂ ≃ D) (g : GL D k) :
    (invT (glTrEquiv j e g)).val = trM j e e (invT g).val := by
  have h1 : (invT (glTrEquiv j e g)).val = ((glTrEquiv j e g)⁻¹).valᵀ := rfl
  have h2 : (invT g).val = (g⁻¹).valᵀ := rfl
  rw [h1, h2, ← map_inv, glTrEquiv_val]
  rfl

end

theorem fFun_trM : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂] [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k'] (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D) (μ₂ : Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D), (∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) → ∀ (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ), (∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) → ∀ (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k), fFun μ₂ σ₂ ν₂ Ψ (trM j rA cD Z) = fFun (pullMeas hj rA' μ₂) σ ν (fun Y => Ψ (trM j rA' cD Y)) Z := by
  intro k k' _ _ _ _ _ _ _ _ j A A' D A₂ A₂' D₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj rA rA' cD μ₂ _ σ₂ σ hσ ν₂ ν hν Ψ Z
  have hcard : Fintype.card D₂ = Fintype.card D := Fintype.card_congr cD
  have hX : ∀ M : Matrix D D k, trM j rA cD (X0 k σ * M) = X0 k' σ₂ * trM j cD cD M := fun M => by
    ext r c
    rw [trM_apply, frameMatrixFirstColumnBlock_mul_apply, frameMatrixFirstColumnBlock_mul_apply, trM_apply, hσ]; rfl
  have hY : ∀ M : Matrix D D k, trM j rA' cD (Y0 k σ * M) = Y0 k' σ₂ * trM j cD cD M := fun M => by
    ext r c
    rw [trM_apply, frameMatrixSecondColumnBlock_mul_apply, frameMatrixSecondColumnBlock_mul_apply, trM_apply, hσ]; rfl
  have hS : ∀ Y : Matrix A' D k, smallF μ₂ ν₂ Ψ (trM j rA' cD Y) =
      smallF (pullMeas hj rA' μ₂) ν (fun Y => Ψ (trM j rA' cD Y)) Y := fun Y => by
    conv_lhs => rw [← map_pullMeas hj rA' μ₂]
    unfold smallF
    have := integral_map_equiv (μ := pullMeas hj rA' μ₂) (glTr hj rA').toHomeomorph.toMeasurableEquiv
      (fun g => Ψ (g.val * trM j rA' cD Y) * (ν₂ (gdet g) : ℂ) * apow (gdet g) ((Fintype.card D₂ : ℂ) / 2))
    refine Eq.trans this ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show Ψ ((glTrEquiv j rA' g).val * trM j rA' cD Y) * ν₂ (gdet (glTrEquiv j rA' g)) *
      apow (gdet (glTrEquiv j rA' g)) _ = _
    rw [gdet_glTrEquiv_ffun, apow_map hj, ← hν, glTrEquiv_val, ← trM_mul, hcard]
  by_cases h : ∃ h : GL D k, Z = X0 k σ * (invT h).val
  · obtain ⟨h, rfl⟩ := h
    rw [hX, ← invT_glTrEquiv_ffun, splitTheta_fFun_frameFirstBlock_mul, splitTheta_fFun_frameFirstBlock_mul, gdet_glTrEquiv_ffun, apow_map hj, ← hν,
      glTrEquiv_val, ← hY, hS, hcard]
  · have h' : ¬ ∃ h₂ : GL D₂ k', trM j rA cD Z = X0 k' σ₂ * (invT h₂).val := by
      rintro ⟨h₂, H⟩
      obtain ⟨g, rfl⟩ := (glTrEquiv j cD).surjective h₂
      rw [invT_glTrEquiv_ffun, ← hX] at H
      exact h ⟨g, trM_injective j rA cD H⟩
    rw [fFun, fFun, dite_eq_right h, dite_eq_right h']

end GlobalTheory.PureMatch.Transport
end
end

