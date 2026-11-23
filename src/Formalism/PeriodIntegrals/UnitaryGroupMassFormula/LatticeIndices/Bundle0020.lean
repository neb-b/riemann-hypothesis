module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0011

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllOfParts
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

def liftE (r : 𝓞 X.B.I.F) : 𝓞 X.B.I.E :=
  ⟨algebraMap X.B.I.F X.B.I.E (r : X.B.I.F),
    (RingOfIntegers.isIntegral_coe r).map (IsScalarTower.toAlgHom ℤ X.B.I.F X.B.I.E)⟩

theorem liftE_coe (r : 𝓞 X.B.I.F) : ((liftE X r : 𝓞 X.B.I.E) : X.B.I.E) = algebraMap X.B.I.F X.B.I.E (r : X.B.I.F) := rfl

def starE (a : 𝓞 X.B.I.E) : 𝓞 X.B.I.E :=
  ⟨star (a : X.B.I.E), (RingOfIntegers.isIntegral_coe a).map (starRingEnd X.B.I.E).toIntAlgHom⟩

theorem hform_zero_left (x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J 0 x = 0 := by
  simp [Formalism.UG.hform]

theorem hform_add_left (y y' x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (y + y') x =
      Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x + Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y' x := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_left (a : 𝓞 X.B.I.E) (y x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (a • y) x =
      star (a : X.B.I.E) * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x := by
  simp only [Formalism.UG.hform, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show star ((a • y) i) * X.B.I.J i j * x j = star (a : X.B.I.E) * (star (y i) * X.B.I.J i j * x j)
  rw [Pi.smul_apply, Algebra.smul_def]
  show star ((a : X.B.I.E) * y i) * _ * _ = _
  rw [star_mul']
  ring

theorem locGlob_of (hN : DenomP X p θ) : LocGlob X p θ := by
  classical
  intro x hx
  obtain ⟨S, hS⟩ := X.B.I.L_fg
  have hSL : ∀ g ∈ S, g ∈ X.B.I.L := fun g hg => hS ▸ Submodule.subset_span hg
  have hg : ∀ g ∈ S, ∃ s : 𝓞 X.B.I.F, s ∉ p.1.asIdeal ∧ ∃ c : 𝓞 X.B.I.E,
      (c : X.B.I.E) = algebraMap X.B.I.F X.B.I.E s * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J g x :=
    fun g hgS => hN _ (hx g (hSL g hgS)).1 (hx g (hSL g hgS)).2
  choose! s hs c hc using hg
  set t : 𝓞 X.B.I.F := ∏ g ∈ S, s g with ht_def
  have ht : t ∉ p.1.asIdeal := by
    intro h
    have := p.1.isPrime
    obtain ⟨g, hgS, hg⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hs g hgS hg
  set T : X.B.I.E := algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) with hT
  have hkey : ∀ g ∈ S, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J g (T • x) ∈
      (algebraMap (𝓞 X.B.I.E) X.B.I.E).range := by
    intro g hgS
    rw [hform_smul_right]
    refine ⟨liftE X (∏ h ∈ S.erase g, s h) * c g, ?_⟩
    rw [map_mul]
    show ((liftE X (∏ h ∈ S.erase g, s h) : 𝓞 X.B.I.E) : X.B.I.E) * ((c g : 𝓞 X.B.I.E) : X.B.I.E) = _
    rw [hc g hgS, liftE_coe, hT, ht_def, ← Finset.mul_prod_erase S s hgS]
    have hm : ((s g * ∏ x ∈ S.erase g, s x : 𝓞 X.B.I.F) : X.B.I.F) =
        (s g : X.B.I.F) * ((∏ x ∈ S.erase g, s x : 𝓞 X.B.I.F) : X.B.I.F) := map_mul (algebraMap _ _) _ _
    rw [hm, map_mul]
    ring
  have hTx : T • x ∈ X.B.I.L := by
    refine (X.B.I.L_dual _).2 fun y hy => ?_
    rw [← hS] at hy
    induction hy using Submodule.span_induction with
    | mem g hg => exact hkey g hg
    | zero => rw [hform_zero_left]; exact ⟨0, map_zero _⟩
    | add y y' _ _ h1 h2 =>
        obtain ⟨c1, e1⟩ := h1
        obtain ⟨c2, e2⟩ := h2
        exact ⟨c1 + c2, by rw [map_add (f := _), e1, e2, hform_add_left]⟩
    | smul a y _ h1 =>
        obtain ⟨c1, e1⟩ := h1
        exact ⟨starE X a * c1, by rw [map_mul, e1, hform_smul_left]; rfl⟩
  obtain ⟨hinv, hne⟩ := unit_of_notMem X p t ht
  have hM : (fun j => iota2 X p θ ((T • x) j)) ∈ Mlat2 X p θ := Submodule.subset_span ⟨T • x, hTx, rfl⟩
  have heq : (fun j => iota2 X p θ (x j)) =
      (⟨(algebraMap X.B.I.F (FpX X p) (t : X.B.I.F))⁻¹, hinv⟩ : OpX X p) • (fun j => iota2 X p θ ((T • x) j)) := by
    funext j
    show iota2 X p θ (x j) = (algebraMap X.B.I.F (FpX X p) (t : X.B.I.F))⁻¹ * iota2 X p θ (T * x j)
    rw [map_mul, hT, secondEmbedding_algebraMap, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [heq]
  exact Submodule.smul_mem _ _ hM

theorem latBasisAll_of_parts
    (hN : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → DenomP X p θ)
    (hA : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → ApproxP X p θ) :
    LatBasisAll X p := latBasisAll_of_back X p (fun θ hθ => dualBack_of X p θ (locGlob_of X p θ (hN θ hθ)) (hA θ hθ))

end Loc

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfTransitive
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix

section Loc

variable {D : D7} (X : HidaSetting D)

def TransA (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
    (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) (π : Op X p →+* ZMod (gOf p)) : Prop :=
  ∀ x : HAp X p, x ∈ KvX X p → ∀ Y : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p),
    ((glRed (algebraMap (Op X p) (FpX X p)) Y : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
        Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
      ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
          Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
        (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) →
    (LocCong X p x ↔ glRed π Y ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k)

def StTransA (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧
      ∃ π : Op X p →+* ZMod (gOf p), Function.Surjective π ∧
        RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)} ∧ TransA X p θ Q π

theorem stFrameA_of_trans (hC : LatCoreX) (p : TypX X) (h : StTransA X p) : StFrameA X p := by
  obtain ⟨θ, hθ, Q, hL, π, hπ, hker, hT⟩ := h
  obtain ⟨ψ, hψ, hk, hform⟩ := hC X p θ hθ Q hL (stK_holds X p).choose (stK_holds X p).choose_spec.1
  refine ⟨π, hπ, hker, (stK_holds X p).choose, (stK_holds X p).choose_spec.1, ψ, hψ, hk, 1, fun x => ?_⟩
  rw [map_one, inv_one, one_mul, mul_one]
  have hx : (x : HAp X p) ∈ KvX X p :=
    (Set.ext_iff.mp (stK_holds X p).choose_spec.1 (x : HAp X p)).1 x.2
  exact hT x hx (ψ x) (hform x)

end Loc

end MassDataIdxSteps
end
end

