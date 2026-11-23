module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St.G.FrameClose

variable {I : AutInst}

theorem hform_mulVec_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have e : ∀ (N : Matrix n n A) (u v : n → A), Formalism.UG.hform σ N u v = (σ ∘ u) ⬝ᵥ (N *ᵥ v) := by
    intro N u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [e, e, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

theorem hA_unitary (x : I.Gf) (v w : VA I) :
    Formalism.L2.SG.HidaSetting.hA I (I.fmat x *ᵥ v) (I.fmat x *ᵥ w) = Formalism.L2.SG.HidaSetting.hA I v w := by
  unfold Formalism.L2.SG.HidaSetting.hA
  rw [hform_mulVec_mulVec]
  have h : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
      I.fmat x = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  rw [h]

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp [AutInst.fmat]

theorem hA_move (x : I.Gf) (v w : VA I) :
    Formalism.L2.SG.HidaSetting.hA I v (I.fmat x *ᵥ w) = Formalism.L2.SG.HidaSetting.hA I (I.fmat x⁻¹ *ᵥ v) w := by
  rw [← hA_unitary x (I.fmat x⁻¹ *ᵥ v) w, mulVec_mulVec, fmat_mul_inv, one_mulVec]

theorem hA_sub_left (v v' w : VA I) :
    Formalism.L2.SG.HidaSetting.hA I (v - v') w = Formalism.L2.SG.HidaSetting.hA I v w - Formalism.L2.SG.HidaSetting.hA I v' w := by
  simp only [Formalism.L2.SG.HidaSetting.hA, Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hA_nat_left (c : ℕ) (v w : VA I) :
    Formalism.L2.SG.HidaSetting.hA I ((c : I.E ⊗[I.F] Af I.F) • v) w = (c : I.E ⊗[I.F] Af I.F) * Formalism.L2.SG.HidaSetting.hA I v w := by
  simp only [Formalism.L2.SG.HidaSetting.hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast,
    Finset.mul_sum, mul_assoc]

theorem hA_int {v w : VA I} (hv : v ∈ I.Lf) (hw : w ∈ I.Lf) : Formalism.L2.SG.HidaSetting.hA I v w ∈ IntAf I.F I.E :=
  (GlobalTheory.AdelicLattice.adelicLattice_selfDual I w).1 hw v hv

theorem nat_smul_mem (c : ℕ) {v : VA I} (hv : v ∈ I.Lf) : (c : I.E ⊗[I.F] Af I.F) • v ∈ I.Lf := by
  rw [Nat.cast_smul_eq_nsmul]
  exact I.Lf.nsmul_mem hv c

theorem mL_le (g : ℕ) : Formalism.L2.SG.HidaSetting.mL I g ≤ I.Lf := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.RowIndex.mem_mL.1 hx
  exact nat_smul_mem g hz

theorem zmod_of_mL {g : ℕ} {x w : VA I} (hx : x ∈ Formalism.L2.SG.HidaSetting.mL I g) (hw : w ∈ I.Lf) :
    ZMod' I g (Formalism.L2.SG.HidaSetting.hA I x w) := by
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.RowIndex.mem_mL.1 hx
  rw [hA_nat_left]
  exact ⟨_, hA_int hz hw, rfl⟩

theorem den_of_inAt {g : ℕ} {w0 w : VA I} (hw0 : w0 ∈ I.Lf) (h : InAt I g g (w0 - w)) :
    ∃ c : ℕ, Nat.Coprime c g ∧ (c : I.E ⊗[I.F] Af I.F) • w ∈ I.Lf := by
  obtain ⟨c, hc, hm⟩ := h
  refine ⟨c, hc, ?_⟩
  have e : (c : I.E ⊗[I.F] Af I.F) • w = (c : I.E ⊗[I.F] Af I.F) • w0 - (c : I.E ⊗[I.F] Af I.F) • (w0 - w) := by
    rw [smul_sub]; abel
  rw [e]
  exact sub_mem (nat_smul_mem c hw0) (mL_le g hm)

theorem inAt_pair {g : ℕ} {β v0 v w : VA I} (hβ : β ∈ I.Lf) (hv : InAt I g g (v0 - v))
    (h0 : ZMod' I g (Formalism.L2.SG.HidaSetting.hA I v0 β))
    (hw : ∃ c : ℕ, Nat.Coprime c g ∧ (c : I.E ⊗[I.F] Af I.F) • w ∈ I.Lf) :
    InAt I g g (Formalism.L2.SG.HidaSetting.hA I v β • w) := by
  obtain ⟨c1, hc1, h1⟩ := hv
  obtain ⟨t0, ht0, e0⟩ := h0
  obtain ⟨c2, hc2, h2⟩ := hw
  obtain ⟨t1, ht1, e1⟩ := zmod_of_mL h1 hβ
  rw [hA_nat_left, hA_sub_left, e0] at e1
  have key : (c1 : I.E ⊗[I.F] Af I.F) * Formalism.L2.SG.HidaSetting.hA I v β =
      (g : I.E ⊗[I.F] Af I.F) * ((c1 : I.E ⊗[I.F] Af I.F) * t0 - t1) := by
    linear_combination -e1
  have hm : (c1 : I.E ⊗[I.F] Af I.F) * t0 - t1 ∈ IntAf I.F I.E :=
    sub_mem (mul_mem (natCast_mem _ c1) ht0) ht1
  refine ⟨c1 * c2, Nat.Coprime.mul_left hc1 hc2, ?_⟩
  have e : ((c1 * c2 : ℕ) : I.E ⊗[I.F] Af I.F) • (Formalism.L2.SG.HidaSetting.hA I v β • w) =
      ((c1 : I.E ⊗[I.F] Af I.F) * t0 - t1) • ((g : I.E ⊗[I.F] Af I.F) • ((c2 : I.E ⊗[I.F] Af I.F) • w)) := by
    rw [smul_smul, smul_smul, smul_smul, Nat.cast_mul]
    congr 1
    linear_combination (c2 : I.E ⊗[I.F] Af I.F) * key
  rw [e]
  exact (Formalism.L2.SG.HidaSetting.mL I g).smul_mem (⟨_, hm⟩ : IntAf I.F I.E) (Submodule.subset_span ⟨_, h2, rfl⟩)

end GlobalTheory.St.G.FrameClose

namespace GlobalTheory.St.G.FrameClose

variable {D : D7}

theorem transported_close (X : HidaSetting D) (u : D.what₂.Word) {β : VA X.B.I} (hβ : β ∈ X.B.I.Lf)
    (hz : ZMod' X.B.I X.B.g (Formalism.L2.SG.HidaSetting.hA X.B.I X.z0 β))
    (he : ∀ a, ZMod' X.B.I X.B.g (Formalism.L2.SG.HidaSetting.hA X.B.I (X.e0 a) β))
    (hf : ∀ a, ZMod' X.B.I X.B.g (Formalism.L2.SG.HidaSetting.hA X.B.I (X.f0 a) β))
    (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I)
    (H : ∀ y ∈ X.B.I.Lf, (∀ a, InAt X.B.I X.B.g X.B.g
        (Formalism.L2.SG.HidaSetting.hA X.B.I (Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a)) y • Formalism.L2.SG.HidaSetting.incl X.B.I (X.fR a)) ∧
        InAt X.B.I X.B.g X.B.g
        (Formalism.L2.SG.HidaSetting.hA X.B.I (Formalism.L2.SG.HidaSetting.incl X.B.I (X.fR a)) y • Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a))) →
      InAt X.B.I X.B.g X.B.g
        (Formalism.L2.SG.HidaSetting.hA X.B.I (Formalism.L2.SG.HidaSetting.incl X.B.I (X.zR u)) y • Formalism.L2.SG.HidaSetting.incl X.B.I (X.zR u)) →
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y - y ∈ Formalism.L2.SG.HidaSetting.mL X.B.I X.B.g) :
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ β) - X.B.I.fmat (X.xu u) *ᵥ β ∈
      Formalism.L2.SG.HidaSetting.mL X.B.I X.B.g := by
  obtain ⟨hef, hz0, -⟩ := X.vectorsInLattice
  refine H _ ((X.xu_K u β).1 hβ) (fun a => ⟨?_, ?_⟩) ?_
  · have hfix : X.B.I.fmat (X.xu u) *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a) =
        Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a) := (X.xu_fix u a).1
    have hu := hA_unitary (X.xu u) (Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a)) β
    rw [hfix] at hu
    rw [hu]
    exact inAt_pair hβ (X.basisApprox a).1 (he a) (den_of_inAt (hef a).2 (X.basisApprox a).2)
  · have hfix : X.B.I.fmat (X.xu u) *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.fR a) =
        Formalism.L2.SG.HidaSetting.incl X.B.I (X.fR a) := (X.xu_fix u a).2
    have hu := hA_unitary (X.xu u) (Formalism.L2.SG.HidaSetting.incl X.B.I (X.fR a)) β
    rw [hfix] at hu
    rw [hu]
    exact inAt_pair hβ (X.basisApprox a).2 (hf a) (den_of_inAt (hef a).1 (X.basisApprox a).1)
  · rw [hA_move]
    obtain ⟨c', hc', hm⟩ := X.xu_z u
    have hv : InAt X.B.I X.B.g X.B.g
        (X.z0 - X.B.I.fmat (X.xu u)⁻¹ *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.zR u)) := by
      refine ⟨c', hc', ?_⟩
      rw [← neg_sub, smul_neg]
      exact neg_mem hm
    refine inAt_pair hβ hv hz ?_
    obtain ⟨d, hd, hdm⟩ := den_of_inAt hz0 hv
    refine ⟨d, hd, ?_⟩
    have h := (X.xu_K u _).1 hdm
    rwa [mulVec_smul, mulVec_mulVec, fmat_mul_inv, one_mulVec] at h

theorem typeVec_close : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), (∀ y ∈ X.B.I.Lf, (∀ a, InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a)) ∧ InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a))) → InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u)) → (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y - y ∈ mL X.B.I X.B.g) → (∀ i, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g ∧ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) := by
  intro D X u wt ιA _ _ c p H i
  obtain ⟨-, -, hb⟩ := X.vectorsInLattice
  exact ⟨transported_close X u (hb i).1 (X.weightVectorsIntegral i).1 (fun a => ((X.weightVectorsIntegral i).2.2 a).1)
      (fun a => ((X.weightVectorsIntegral i).2.2 a).2.1) c p H,
    transported_close X u (hb i).2 (X.weightVectorsIntegral i).2.1 (fun a => ((X.weightVectorsIntegral i).2.2 a).2.2.1)
      (fun a => ((X.weightVectorsIntegral i).2.2 a).2.2.2) c p H⟩

end GlobalTheory.St.G.FrameClose
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PureFiniteAdelicTestFunctionContinuousCompact
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.PureFinite

open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport GlobalTheory.GaugeEx Set

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}

include b in
theorem continuous_projV_fin (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (fun X : Fin n → Fin M → Af F ⊗[F] E => projV v X) := by
  have h : Continuous (evalV F v) :=
    RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v
  haveI : IsTopologicalRing (Af F) := inferInstance
  have h2 : Continuous (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)) :=
    continuous_map_tens b (evalV F v) h
  exact continuous_pi fun a => continuous_pi fun i =>
    h2.comp ((continuous_apply i).comp (continuous_apply a))

theorem projV_add (v : HeightOneSpectrum (𝓞 F)) (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    projV v (X + Y) = projV v X + projV v Y := by
  funext a i
  simp [projV, map_add (f := _)]

theorem latV_add (v : HeightOneSpectrum (𝓞 F)) {Y Z : Fin n → Fin M → Fv F v ⊗[F] E}
    (hY : Y ∈ latV b v) (hZ : Z ∈ latV b v) : Y + Z ∈ latV b v := by
  intro a i k
  simp only [Pi.add_apply, map_add (f := _), Finsupp.add_apply]
  exact add_mem (hY a i k) (hZ a i k)

variable (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)

theorem continuous_finprod (hSB : ∀ v, IsSB (Φv v))
    (hae : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) :
    Continuous (fun X : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v X)) := by
  classical
  rw [continuous_iff_continuousAt]
  intro X
  have hS := Filter.eventually_cofinite.1 (hae.and (eventually_mem_latV b X))
  let O : Set (Af F) := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}
  have hOo : IsOpen O :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  let U : Set (Fin n → Fin M → Af F ⊗[F] E) := {Y | ∀ a i k, crd b (Af F) ((Y - X) a i) k ∈ O}
  have hUo : IsOpen U := by
    have e : U = ⋂ a, ⋂ i, ⋂ k, (fun Y : Fin n → Fin M → Af F ⊗[F] E =>
        crd b (Af F) ((Y - X) a i) k) ⁻¹' O := by
      ext Y; simp [U]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun k => hOo.preimage ((continuous_crd b (Af F) k).comp
        ((continuous_apply i).comp ((continuous_apply a).comp (continuous_id.sub continuous_const))))
  have hXU : X ∈ U := by
    intro a i k v
    simp only [sub_self, crd, Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem (v.adicCompletionIntegers F)
  have hev : (fun Y : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v Y)) =ᶠ[nhds X]
      fun Y => ∏ v ∈ hS.toFinset, Φv v (projV v Y) := by
    filter_upwards [hUo.mem_nhds hXU] with Y hY
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    rw [Set.Finite.coe_toFinset]
    intro h
    apply hv
    have hYX : projV v (Y - X) ∈ latV b v := by
      intro a i k
      have := crd_projV b (Y - X) v a i k
      simp only [crd] at this
      rw [this]
      exact hY a i k v
    have hmem : projV v Y ∈ latV b v := by
      have e : projV v Y = projV v (Y - X) + projV v X := by
        rw [← projV_add]; simp
      rw [e]
      exact latV_add b v hYX h.2
    show Φv v (projV v Y) = 1
    rw [h.1, Set.indicator_of_mem hmem]
    rfl
  refine ContinuousAt.congr ?_ hev.symm
  exact (continuous_finsetProd _ fun v _ =>
    (hSB v).1.continuous.comp (continuous_projV_fin b v)).continuousAt

theorem hasCompactSupport_finprod (hSB : ∀ v, IsSB (Φv v))
    (hae : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) :
    HasCompactSupport (fun X : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v X)) := by
  classical
  let D : Fin n → Fin M → Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
    fun i j k v =>
      ((fun Z : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Z i j) k) '' tsupport (Φv v)) ∪
        (v.adicCompletionIntegers F : Set (Fv F v))
  have hD : ∀ i j k v, IsCompact (D i j k v) := fun i j k v =>
    ((hSB v).2.isCompact.image ((continuous_crd b (Fv F v) k).comp
      ((continuous_apply j).comp (continuous_apply i)))).union
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
  have hDe : ∀ i j k, ∀ᶠ v in Filter.cofinite,
      D i j k v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro i j k
    filter_upwards [hae] with v hv
    refine Set.union_eq_right.2 ?_
    rintro _ ⟨Z, hZ, rfl⟩
    have hsub : tsupport (Φv v) ⊆ latV b v := by
      rw [hv]
      exact closure_minimal Set.support_indicator_subset (isClopen_latV b v n M).isClosed
    exact hsub hZ i j k
  let Bf : Fin n → Fin M → Fin d → Set (Af F) := fun i j k => {x | ∀ v, x v ∈ D i j k v}
  have hBf : ∀ i j k, IsCompact (Bf i j k) := fun i j k => isCompact_finBox (hD i j k) (hDe i j k)
  let Box : Set (Fin n → Fin M → Fin d → Af F) :=
    Set.pi univ fun i => Set.pi univ fun j => Set.pi univ fun k => Bf i j k
  have hbox : IsCompact Box := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    isCompact_univ_pi fun k => hBf i j k
  let L : (Fin n → Fin M → Fin d → Af F) → (Fin n → Fin M → Af F ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af F) ⊗ₜ[F] b k)
  have hL : Continuous L := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  refine HasCompactSupport.intro (hbox.image hL) fun X hX => ?_
  by_contra h
  apply hX
  have hv := factor_ne_zero b Φv hae X h
  refine ⟨fun i j k => crd b (Af F) (X i j) k, ?_, ?_⟩
  · simp only [Box, Set.mem_pi, Set.mem_univ, true_implies]
    intro i j k v
    refine Or.inl ⟨projV v X, subset_tsupport _ (hv v), ?_⟩
    exact crd_projV b X v i j k
  · funext i j
    exact (eq_sum_crd b (Af F) (X i j)).symm

end GlobalTheory.PureFinite

namespace GlobalTheory

theorem isPureFin_continuous_hasCompactSupport : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (d M n : ℕ) (b : Module.Basis (Fin d) F E)
    (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
    IsPureFin b Φf Φv → Continuous Φf ∧ HasCompactSupport Φf := by
  intro F E _ _ _ _ _ d M n b Φf Φv h
  obtain ⟨hSB, hae, hprod⟩ := h
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have e : Φf = fun X => ∏ᶠ v, Φv v (projV v X) := funext hprod
  subst e
  exact ⟨PureFinite.continuous_finprod b Φv hSB hae, PureFinite.hasCompactSupport_finprod b Φv hSB hae⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReproducingFormulaDiscreteSeriesTestGrowth
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Reproducing

theorem two_mul_rank_le {n : ℕ} (ε : Fin n → Bool) : 2 * rkR ε ≤ n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  unfold rkR
  omega

theorem weight_condition (B : RowsAut) (h s : ℝ) (hn : 1 ≤ B.I.n) (hb : HBig B 40 h)
    (hs : s ≤ 2 * (B.I.n : ℝ) ^ 2) (v : InfinitePlace B.I.F) :
    rkR (B.I.ε v) = 0 ∨ 8 * Real.sqrt (rkR (B.I.ε v)) * (s + 4 * B.I.n * rkR (B.I.ε v)) < h := by
  rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with h0 | h0
  · exact Or.inl h0
  right
  have h1 : (2 : ℝ) * rkR (B.I.ε v) ≤ B.I.n := by exact_mod_cast two_mul_rank_le _
  have h2 : 0 < Real.sqrt (rkR (B.I.ε v)) := Real.sqrt_pos.2 (by exact_mod_cast h0)
  have h3 : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have h4 := hb v
  have h5 : s + 4 * B.I.n * rkR (B.I.ε v) ≤ 4 * (B.I.n : ℝ) ^ 2 := by nlinarith
  have h6 := mul_le_mul_of_nonneg_left h5 h2.le
  have h7 : 0 < Real.sqrt (rkR (B.I.ε v)) * (B.I.n : ℝ) ^ 2 := by positivity
  nlinarith

theorem inv_tau_pow_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 ∈ I.Kset) :
    (tau1 I (x * g))⁻¹ ^ (2 * I.n ^ 2 * I.f) ≤
      (tau1 I x)⁻¹ ^ (2 * I.n ^ 2 * I.f) * Real.exp (2 * (I.n : ℝ) ^ 2 * dSum I g.1) := by
  obtain ⟨hp, -, -, hl⟩ := _root_.GlobalTheory.TauLipschitz.tauLip I hn
  have hf : (0 : ℝ) < I.f := by
    have : 0 < I.f := Module.finrank_pos
    exact_mod_cast this
  have h1 := (abs_le.1 (hl x g hg)).1
  have h2 : (tau1 I (x * g))⁻¹ ≤ (tau1 I x)⁻¹ * Real.exp (dSum I g.1 / I.f) := by
    rw [← Real.exp_log (inv_pos.2 (hp (x * g))), ← Real.exp_log (inv_pos.2 (hp x)), ← Real.exp_add,
      Real.log_inv, Real.log_inv]
    exact Real.exp_le_exp.2 (by linarith)
  refine (pow_le_pow_left₀ (inv_pos.2 (hp _)).le h2 _).trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  field_simp

theorem isContRep_sum (B : RowsAut) {m : ℕ} (y : Fin m → B.I.L2 B.μf B.fund) (F : Fin m → B.I.GA → ℂ)
    (hF : ∀ i, IsContRep B (y i) (F i)) (c : Fin m → ℂ) :
    IsContRep B (∑ i, c i • y i) (fun x => ∑ i, c i * F i x) := by
  refine ⟨continuous_finsetSum _ fun i _ => continuous_const.mul (hF i).1, fun γ hγ x => ?_, ?_⟩
  · exact Finset.sum_congr rfl fun i _ => by rw [(hF i).2.1 γ hγ]
  · have h1 := Lp.coeFn_finsetSum (univ : Finset (Fin m)) (fun i => c i • y i)
    have h2 : ∀ᵐ x ∂((B.I.muA B.μf).restrict B.fund), ∀ i, (c i • y i : B.I.L2 B.μf B.fund) x = c i * F i x :=
      ae_all_iff.2 fun i => by
        filter_upwards [Lp.coeFn_smul (c i) (y i), (hF i).2.2] with x hx hx'
        rw [hx, Pi.smul_apply, hx', smul_eq_mul]
    filter_upwards [h1, h2] with x hx hx'
    rw [hx, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hx' i

theorem reproducing_formula : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), IsContRep B (T y) f → (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) ∧ (∃ Φ : B.I.GA → ℝ, Integrable Φ (B.I.muA B.μf) ∧ ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g) ∧ ∀ x, f x = ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
  intro B d h hd hn hdec hb hfin T hT y f hf
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨hl, -⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular B.I B.μf
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  obtain ⟨hp, htc, -, -⟩ := _root_.GlobalTheory.TauLipschitz.tauLip B.I hn
  obtain ⟨hphc, hphb, hphi⟩ := _root_.GlobalTheory.Dec.PhMajProof.phMaj B d h hd hdec
  have hec : Continuous B.e := (GlobalTheory.rowsAut_idem_elementary B).2.2.2
  have hb' : HBig B 32 h := fun v => le_trans (by
    have : 0 ≤ (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by positivity
    nlinarith) (hb v)
  obtain ⟨u, F, -, hsp, hF, -, -, -, hbd⟩ := _root_.GlobalTheory.KernelExpansion.kernelB B d h hd hn hdec hb' hfin T hT
  have hmem : T y ∈ Submodule.span ℂ (Set.range u) := by rw [hsp]; exact ⟨y, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  obtain ⟨hext, huniq, -⟩ := GlobalTheory.ExtContRep.ext_ae_eq_contRep B (T y) f hf
  have hfe : (fun x => ∑ i, c i * F i x) = f := huniq _ (hc ▸ isContRep_sum B u F hF c)
  set N := 2 * B.I.n ^ 2 * B.I.f with hN
  have hτ : ∀ x, 0 ≤ (tau1 B.I x)⁻¹ ^ N := fun x => pow_nonneg (inv_pos.2 (hp x)).le _
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ N := by
    refine ⟨Real.sqrt ((∑ i, ‖c i‖ ^ 2) * kerC B d), Real.sqrt_nonneg _, fun x => ?_⟩
    have h1 := hbd c x
    rw [congrFun hfe x, show 4 * B.I.n ^ 2 * B.I.f = N * 2 by rw [hN]; ring, pow_mul, ← mul_assoc] at h1
    have h2 := Real.le_sqrt_of_sq_le h1
    rwa [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (hτ x)] at h2
  let Φ : B.I.GA → ℝ := fun g =>
    C * (majPh B d h g.1 * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1) * ‖B.e g.2‖)
  have hm0 : ∀ g, 0 ≤ majPh B d h g := fun g => (norm_nonneg _).trans (hphb g)
  have hΦ0 : ∀ g, 0 ≤ Φ g := fun g =>
    mul_nonneg hC0 (mul_nonneg (mul_nonneg (hm0 _) (Real.exp_pos _).le) (norm_nonneg _))
  have hΦi : Integrable Φ (B.I.muA B.μf) :=
    (Integrable.mul_prod (hphi _ (by positivity) (weight_condition B h _ hn hb le_rfl))
      B.Re_spec.1.norm).const_mul C
  have hΦ : ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ N * Φ g := by
    intro x g
    by_cases he : B.e g.2 = 0
    · rw [phe, he, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg (hτ x) (hΦ0 g)
    have hg : g.2 ∈ B.I.Kset := B.e_adm.2.2.2.2.1 _ he
    have h1 := (hC (x * g)).trans (mul_le_mul_of_nonneg_left (inv_tau_pow_le B.I hn x g hg) hC0)
    rw [norm_mul, phe, norm_mul]
    calc _ ≤ (majPh B d h g.1 * ‖B.e g.2‖) *
          (C * ((tau1 B.I x)⁻¹ ^ N * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hphb _) (norm_nonneg _)) h1 (norm_nonneg _)
            (mul_nonneg (hm0 _) (norm_nonneg _))
      _ = _ := by simp only [Φ]; ring
  refine ⟨⟨C, hC⟩, ⟨Φ, hΦi, hΦ⟩, fun x => (congrFun (huniq (fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf))
    ⟨?_, fun γ hγ x => ?_, ?_⟩) x).symm⟩
  · have hpc : Continuous (phe B d) := (hphc.comp continuous_fst).mul (hec.comp continuous_snd)
    have htN : Continuous fun x => (tau1 B.I x)⁻¹ ^ N := (htc.inv₀ fun x => (hp x).ne').pow _
    refine continuous_iff_continuousAt.2 fun x₀ => ?_
    refine continuousAt_of_dominated (bound := fun g => ((tau1 B.I x₀)⁻¹ ^ N + 1) * Φ g)
      (Filter.Eventually.of_forall fun x => ?_) ?_ (hΦi.const_mul _) (Filter.Eventually.of_forall fun g => ?_)
    · exact (hpc.mul (hf.1.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    · filter_upwards [htN.continuousAt.eventually_lt continuousAt_const (lt_add_one ((tau1 B.I x₀)⁻¹ ^ N))]
        with x hx
      exact Filter.Eventually.of_forall fun g => (hΦ x g).trans (mul_le_mul_of_nonneg_right hx.le (hΦ0 g))
    · exact (continuous_const.mul (hf.1.comp (continuous_id.mul continuous_const))).continuousAt
  · simp only [mul_assoc, hf.2.1 γ hγ]
  · have hi : Integrable (ph B d) (muInf B.I) := by
      refine (hphi 0 le_rfl (weight_condition B h _ hn hb (by positivity))).mono' hphc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun g => ?_)
      simpa using hphb g
    have hproj := ((_root_.GlobalTheory.GlobProj.globalProj_holds B d hd hi).2.2.2 T hT).1
    have hTT : T (T y) = T y := congrArg (fun A : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => A y) hproj.1
    have h1 := (GlobalTheory.ConvKernel.rconv_eq_integral B _ T hT (T y)).2
    rw [hTT] at h1
    refine h1.trans (Filter.Eventually.of_forall fun x => integral_congr_ae ?_)
    filter_upwards [(measurePreserving_mul_left (B.I.muA B.μf) x).quasiMeasurePreserving.ae hext] with g hg
    rw [hg]

end GlobalTheory.Reproducing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetIntegralStabilizerExists
section
noncomputable section
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fundC_holds : FundC := by
  intro D X Y u t
  obtain ⟨K, hK⟩ : ∃ Ω, IsSFund X.B.I (ROinf t) Ω := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u t
  set Γ0 := Formalism.L2.SG.Pf.ROsub X (X.Fu u) (X.Fu u) t.lam t.lam' t.lin with hΓ0
  refine ⟨K, hK.1, fun r _ => ?_⟩
  obtain ⟨s0, hs0, hs0F⟩ := hK.2.1 r
  refine ⟨s0, ⟨hs0, hs0F⟩, fun s' ⟨hs', hs'F⟩ => ?_⟩
  have h2 : (s0 * s'⁻¹) * (s' * r) ∈ K := by simpa [mul_assoc] using hs0F
  have := hK.2.2 _ hs'F _ (Γ0.mul_mem hs0 (Γ0.inv_mem hs')) h2
  exact (mul_inv_eq_one.1 this).symm

end GlobalTheory.TypeAsm
end
end

