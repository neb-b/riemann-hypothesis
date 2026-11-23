module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosets

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.UnitaryBC.ClassTransport
open scoped TensorProduct

namespace GlobalTheory.FormDict.Model

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "F₀" => maximalRealSubfield L

def kappa : AL L ≃+* FiniteAdeleRing (𝓞 L) L :=
  (Algebra.TensorProduct.comm F₀ L (FiniteAdeleRing (𝓞 F₀) F₀)).toRingEquiv.trans (GlobalTheory.LFun.finAdEquiv F₀ L)

theorem kappa_tmul (x : L) (a : FiniteAdeleRing (𝓞 F₀) F₀) :
    kappa L (x ⊗ₜ a) = GlobalTheory.AdeleBaseChange.adMap F₀ L a * algebraMap L _ x :=
  GlobalTheory.LFun.toFinAd_tmul a x

theorem kappa_conj (y : AL L) :
    kappa L (conjAL L y) = conjFin (IsCMField.complexConj L).toRingEquiv (kappa L y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul x a =>
    have hAd : conjFin (IsCMField.complexConj L).toRingEquiv
        (GlobalTheory.AdeleBaseChange.adMap F₀ L a) = GlobalTheory.AdeleBaseChange.adMap F₀ L a := by
      have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField L
      refine congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := F₀)).equalizer
        ((continuous_conjFin _).comp (continuous_adMap F₀ L)) (continuous_adMap F₀ L)
        (funext fun k => ?_)) a
      simp only [Function.comp_apply]
      rw [GlobalTheory.AdeleBaseChange.adMap_algebraMap, conjFin_algebraMap]
      congr 1
      exact IsCMField.complexConj_apply_eq_self L k
    change kappa L ((IsCMField.complexConj L x) ⊗ₜ a) = _
    rw [kappa_tmul, kappa_tmul, map_mul, hAd, conjFin_algebraMap]
    rfl
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), hy, hz, map_add (f := _)]

def psi0 : GAf L n →* GL (Fin n) (FiniteAdeleRing (𝓞 L) L) :=
  (Matrix.GeneralLinearGroup.map (kappa L).toRingHom).comp (ReciprocityTheory.Aut.GA L n).subtype

theorem map_conjT (M : Matrix (Fin n) (Fin n) (AL L)) :
    (conjT (conjAL L) M).map (kappa L).toRingHom =
      Formalism.UG.cT (conjFin (IsCMField.complexConj L).toRingEquiv) (M.map (kappa L).toRingHom) :=
  Matrix.ext fun _ _ => kappa_conj L _

theorem unitaryFinitePointsToGLFiniteAdeles_isUnitary (x : GAf L n) :
    Formalism.UG.cT (conjFin (IsCMField.complexConj L).toRingEquiv) (psi0 L n x).val * (psi0 L n x).val = 1 := by
  have hx : x.1.val * conjT (conjAL L) x.1.val = 1 := x.2
  rw [mul_eq_one_comm] at hx
  change Formalism.UG.cT _ (x.1.val.map (kappa L).toRingHom) * x.1.val.map (kappa L).toRingHom = 1
  rw [← map_conjT, ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero _) (map_one _)]

def j0 : GAf L n →* UA L n :=
  ((finGL L n).comp (psi0 L n)).codRestrict (UA L n) fun x => finGL_mem_UA _ (unitaryFinitePointsToGLFiniteAdeles_isUnitary L n x)

def finIso : FinIso L n where
  κ := kappa L
  left x := by rw [kappa_tmul, map_one, one_mul]
  right w v h := by
    have h' : w.under (𝓞 F₀) = v := HeightOneSpectrum.ext h
    subst h'
    refine ⟨GlobalTheory.LFun.complMap (rfl : w.under (𝓞 F₀) = _), GlobalTheory.LFun.InertChart.continuous_complMap _, fun a => ?_⟩
    rw [kappa_tmul, map_one, mul_one]
    rfl
  j := j0 L n
  fin x := MonoidHom.mem_ker.2 (pInf_finGL (psi0 L n x))
  loc x w s t := by
    have h : Matrix.GeneralLinearGroup.map (pFin L) (j0 L n x).1 = psi0 L n x := pFin_finGL _
    have h2 := congrArg (fun g : GL (Fin n) (Af L) => pLoc L w (g.val s t)) h
    exact h2
  onto g hgf := by
    have hg := g.2
    change Formalism.UG.cT (conjAd L) g.1.val * 1 * g.1.val = 1 at hg
    rw [Matrix.mul_one] at hg
    have hf : Formalism.UG.cT (conjFin (IsCMField.complexConj L).toRingEquiv)
        (Matrix.GeneralLinearGroup.map (pFin L) g.1).val * (Matrix.GeneralLinearGroup.map (pFin L) g.1).val = 1 := by
      have h := congrArg (fun M => M.map (pFin L)) hg
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
      exact h
    let u := Matrix.GeneralLinearGroup.map (kappa L).symm.toRingHom (Matrix.GeneralLinearGroup.map (pFin L) g.1)
    have hU : u.val.map (kappa L).toRingHom = (Matrix.GeneralLinearGroup.map (pFin L) g.1).val :=
      Matrix.ext fun i j => (kappa L).apply_symm_apply _
    have hmem : u ∈ ReciprocityTheory.Aut.GA L n := by
      change u.val * conjT (conjAL L) u.val = 1
      rw [mul_eq_one_comm]
      refine Matrix.map_injective (kappa L).injective ?_
      change Matrix.map _ (kappa L).toRingHom = Matrix.map 1 (kappa L).toRingHom
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), map_conjT, hU]
      exact hf
    refine ⟨⟨u, hmem⟩, Subtype.ext (ga_ext ?_ ?_)⟩
    · exact (pInf_finGL _).trans (MonoidHom.mem_ker.1 hgf).symm
    · exact (pFin_finGL _).trans (Units.ext hU)

variable {L n}

theorem kappa_eq (F G : FinIso L n) : F.κ = G.κ := by
  refine RingEquiv.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]
  | tmul x a =>
    have e : x ⊗ₜ[F₀] a = (x ⊗ₜ[F₀] (1 : AFplus L)) * ((1 : L) ⊗ₜ[F₀] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, F.left, G.left]
    congr 1
    refine FiniteAdeleRing.ext _ fun w => ?_
    obtain ⟨i, hi, h1⟩ := F.right w (w.under (𝓞 F₀)) rfl
    obtain ⟨i', hi', h2⟩ := G.right w (w.under (𝓞 F₀)) rfl
    have key : ∀ k : F₀, (1 : L) ⊗ₜ[F₀] (algebraMap F₀ (AFplus L) k) = (k : L) ⊗ₜ[F₀] (1 : AFplus L) := fun k => by
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      rfl
    have : (i : _ → _) = i' := (HeightOneSpectrum.denseRange_algebraMap F₀ (w.under (𝓞 F₀))).equalizer hi hi'
      (funext fun k => by
        have a1 := h1 (algebraMap F₀ _ k)
        have a2 := h2 (algebraMap F₀ _ k)
        rw [key, F.left] at a1
        rw [key, G.left] at a2
        exact a1.symm.trans a2)
    change F.κ (1 ⊗ₜ a) w = G.κ (1 ⊗ₜ a) w
    rw [h1, h2, this]


end GlobalTheory.FormDict.Model

end
