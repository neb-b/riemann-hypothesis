module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.AdelicSchrodingerTensorEqLocalOfSupportedAt
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace Tw.SchrLoc
open _root_.GlobalTheory

open GlobalTheory.VacAny

theorem eq_atPlace_of_at {F : Type} [Field F] [NumberField F] {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {z : AF F}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z) :
    z = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v z) := by
  have h1 := hz (1 - GlobalTheory.EmbChart.atPlace v 1)
    (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
  conv_lhs => rw [h1]
  rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul]

theorem schr_tens_of_at : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 i)) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 i)) → ∀ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ),
    (∀ x z : κ → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z → r (x + z) = r x) →
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) φ r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v)
        (GlobalTheory.WeilM.schr (GlobalTheory.VacAny.psiV ψ v) (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i), fun i => GlobalTheory.AdelicU.evFin F v (w.2 i)) φ) r := by
  intro F _ _ ψ v κ _ w h1 h2 φ r hr
  funext x
  have hr' : r (x + w.1) = r x := hr x w.1 (fun u hu => funext fun i => h1 i u hu)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) :=
    fun u hu => by
      simp only [smul_eq_mul, mul_add, dotProduct, Finset.mul_sum]
      have hzero (i : κ) : u * w.2 i = 0 := h2 i u hu
      suffices (∑ i, u * (x i * w.2 i)) = 0 ∧
          (∑ i, u * (⅟(2 : AF F) * (w.1 i * w.2 i))) = 0 by
        rw [this.1, this.2, add_zero]
      constructor <;> apply Finset.sum_eq_zero <;> intro i hi
      · calc
          u * (x i * w.2 i) = x i * (u * w.2 i) := by ring
          _ = 0 := by rw [hzero, mul_zero]
      · calc
          u * (⅟(2 : AF F) * (w.1 i * w.2 i)) = (⅟(2 : AF F) * w.1 i) * (u * w.2 i) := by ring
          _ = 0 := by rw [hzero, mul_zero]
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  rw [hr', eq_atPlace_of_at hz, ← psiV_apply]
  have hinv : GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    have h : GlobalTheory.AdelicU.evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
    rwa [map_mul, map_ofNat] at h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_add (f := _), map_mul, map_sum, hinv, Pi.add_apply]
  simp only [mul_comm (⅟(2 : Fv F v))]
  rw [show (fun i => GlobalTheory.AdelicU.evFin F v (x i) + GlobalTheory.AdelicU.evFin F v (w.1 i)) =
    (fun i => GlobalTheory.AdelicU.evFin F v (x i)) + (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i)) from rfl]
  ring

end Tw.SchrLoc
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ContinuousAddCharSymplecticSelfPairingPlaceCoord
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace Tw.ContSymp
open _root_.GlobalTheory

theorem continuous_psi_symp_atPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (o : E) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {M : Type} [Fintype M] (g : M → Matrix (Fin n) (Fin d) E),
    Continuous (fun a : M → v.adicCompletionIntegers F => ψ (⅟(2 : AF F) *
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) o) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB)
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)))) := by
  intro F E _ _ _ _ _ σ ψ hψ n d JA JB o v M _ g
  have ht : ∀ m : M, Continuous (fun a : M → v.adicCompletionIntegers F =>
      GlobalTheory.EmbChart.atPlace v (a m : Fv F v)) :=
    fun m => (GlobalTheory.VacAny.continuous_atPlace v).comp (continuous_subtype_val.comp (continuous_apply m))
  refine hψ.comp ?_
  delta GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.sum_apply, Matrix.smul_apply, map_sum, map_smul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_eq_mul]
  fun_prop

end Tw.ContSymp
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EqAdeleSupportedAtFinitePlaceOfSupportedAt
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace Tw.VacAny
open _root_.GlobalTheory _root_.GlobalTheory.VacAny

theorem eq_atPlace_of_at {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a → a = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v a) := by
  intro h
  have hu : GlobalTheory.AdelicU.evFin F v (1 - GlobalTheory.EmbChart.atPlace v 1) = 0 := by
    rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have h0 : (1 - GlobalTheory.EmbChart.atPlace v 1) • a = 0 := h _ hu
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h0
  conv_lhs => rw [h0]
  rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul]

end Tw.VacAny
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsRationalDarbouxCoordinatesTensorHermitian
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem Tw.RatDarboux.exists_rational_darboux_of_isGood : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d), ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) :=
  fun B hB _ _ X Y r s r' s' hX hY => Tw.RatDarboux.exists_rational_darboux _ B X Y r s r' s' hB hX hY
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.IsLocallyConstantHeisenbergLatticeVacuumFunction
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.HeisLatVac
open _root_.GlobalTheory _root_.GlobalTheory.HeisLatVac

theorem lc_pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 :=
  _root_.UpperTheory.Reformulated.B.P6.r25a.Tw.HeisLatVac.lc_pow_near_one h

theorem lc_exists_open_ker {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ₀ : AddChar K ℂ) (hψ : Continuous ψ₀) : ∃ U₀ : OpenAddSubgroup K, ∀ t ∈ U₀, ψ₀ t = 1 := by
  have hV : {t : K | ‖ψ₀ t - 1‖ < 1 / 2} ∈ nhds (0 : K) :=
    (isOpen_lt (hψ.sub continuous_const).norm continuous_const).mem_nhds (by simp)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hV
  refine ⟨V, fun t ht => lc_pow_near_one fun n => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  exact hV (V.toAddSubgroup.nsmul_mem ht n)

end Tw.HeisLatVac
end
end

