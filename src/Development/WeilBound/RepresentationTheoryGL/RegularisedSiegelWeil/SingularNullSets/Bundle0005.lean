module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.JstTranspose
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LWa1

theorem dense_loc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (hc : ∀ x, σ (σ x) = x) (hne : ∃ z, σ z ≠ z) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Formalism.UG.cT (σ : E →+* E) J = J) (hdet : J.det ≠ 0) :
    Dense {h : HA (Fv F v) σ J | HA.mat (Fv F v) σ J h ∈ HFin (Fv F v) σ J} := by
  classical
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  have : Nontrivial (Fv F v ⊗[F] E) :=
    (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := Fv F v) (B := E)
      (algebraMap F E).injective).nontrivial
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have b1 : IsOpen {x : Fv F v | IsUnit x} := by
    simp only [isUnit_iff_ne_zero]
    exact isOpen_ne
  have b2 : ∀ x : Fv F v, IsUnit x → ContinuousAt Ring.inverse x := by
    intro x hx
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hx.ne_zero
  obtain ⟨h1, h2⟩ := GlobalTheory.RealApprox.units_of_free (A := Fv F v) (R := Fv F v ⊗[F] E)
    (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)) b1 b2
  refine GlobalTheory.RealApprox.dense_unitary (inclR (F := F) (Fv F v)) (σ : E →+* E) (sigR (Fv F v) σ) (fun x => ?_) hc
    hne (fun x => ?_) ?_ (fun y => ?_) h1 h2 J hJ hdet
  · simp [sigR, inclR]
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [sigR, hc]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  · exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ).toLinearMap
  · let S : AddSubgroup (Fv F v ⊗[F] E) :=
      (inclR (F := F) (E := E) (Fv F v)).toAddMonoidHom.range.topologicalClosure
    have hS : IsClosed (S : Set (Fv F v ⊗[F] E)) := AddSubgroup.isClosed_topologicalClosure _
    show y ∈ S
    induction y using TensorProduct.induction_on with
    | zero => exact S.zero_mem
    | add a b ha hb => exact S.add_mem ha hb
    | tmul a x =>
      have hc : Continuous fun a : Fv F v => a ⊗ₜ[F] x := by
        have : (fun a : Fv F v => a ⊗ₜ[F] x) = fun a : Fv F v => a • ((1 : Fv F v) ⊗ₜ[F] x) := by
          funext a
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Continuous.smul (f := fun a : Fv F v => a)
          (g := fun _ : Fv F v => ((1 : Fv F v) ⊗ₜ[F] x : Fv F v ⊗[F] E)) continuous_id continuous_const
      refine DenseRange.induction_on (HeightOneSpectrum.denseRange_algebraMap F v) a
        (p := fun a => a ⊗ₜ[F] x ∈ S) (hS.preimage hc) fun f => ?_
      refine AddSubgroup.le_topologicalClosure _ ⟨f • x, ?_⟩
      show (1 : Fv F v) ⊗ₜ[F] (f • x) = algebraMap F _ f ⊗ₜ[F] x
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem uj_smul {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) {δ : A}
    (hδ : IsUnit δ) : Formalism.UG.UJ σ (δ • J) = Formalism.UG.UJ σ J := by
  ext g
  show Formalism.UG.cT σ g.1 * (δ • J) * g.1 = δ • J ↔ Formalism.UG.cT σ g.1 * J * g.1 = J
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact hδ.smul_left_cancel

theorem jst_cases (D : D7) (n : ℕ) (P : Fin (n + n) → Fin (n + n) → Prop)
    (h : ∀ a b, P (finSumFinEquiv a) (finSumFinEquiv b)) : ∀ i j, P i j := by
  intro i j
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  exact h a b

theorem jst_transpose (D : D7) (n : ℕ) : (Jst D n)ᵀ = -Jst D n := by
  ext i j
  revert i j
  refine jst_cases D n _ fun a b => ?_
  simp only [Jst, blk4, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.neg_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.one_apply, eq_comm]

theorem jst_map (D : D7) (n : ℕ) : (Jst D n).map (D.sp.cm.sig : D.host.E →+* D.host.E) = Jst D n := by
  ext i j
  revert i j
  refine jst_cases D n _ fun a b => ?_
  simp only [Jst, blk4, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.one_apply, apply_ite]

theorem jst_mul (D : D7) (n : ℕ) : Jst D n * Jst D n = -1 := by
  simp only [Jst, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  ext i j
  revert i j
  refine jst_cases D n _ fun a b => ?_
  simp only [Matrix.submatrix_apply, Matrix.neg_apply, Equiv.symm_apply_apply]
  rw [← Matrix.submatrix_one_equiv (finSumFinEquiv.symm : Fin (n + n) ≃ Fin n ⊕ Fin n)]
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.one_apply, Equiv.eq_symm_apply, Equiv.symm_apply_eq, Fin.ext_iff] <;> omega

theorem jst_det (D : D7) (n : ℕ) : (Jst D n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (jst_mul D n)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg, Matrix.det_one, mul_one] at this
  exact (neg_one_pow_ne_zero (R := D.host.E) _) this.symm

theorem sig_sig (D : D7) (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := by
  simp [Formalism.BasicNotions.CMData.sig]

theorem sig_ne (D : D7) : ∃ z, D.sp.cm.sig z ≠ z := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  have hall : ∀ a : D.host.E, a ∈ (algebraMap D.host.F D.host.E).range := fun a =>
    (D.sp.cm.fixed a).1 (by simpa [Formalism.BasicNotions.CMData.sig, starRingEnd_apply] using h a)
  have hbot : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
    ext a
    simp only [Algebra.mem_top, iff_true, Algebra.mem_bot]
    obtain ⟨b, hb⟩ := hall a
    exact ⟨b, hb⟩
  have := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot
  rw [D.sp.cm.deg2] at this
  norm_num at this

theorem exists_skew (D : D7) : ∃ δ : D.host.E, δ ≠ 0 ∧ D.sp.cm.sig δ = -δ := by
  obtain ⟨z, hz⟩ := sig_ne D
  refine ⟨z - D.sp.cm.sig z, sub_ne_zero.2 (Ne.symm hz), ?_⟩
  rw [map_sub, sig_sig]
  ring

theorem approx_loc (D : D7) (n : ℕ) (v : Pl D) (x : GLoc D.sp.cm.sig (Jst D n) v)
    (O : Set (GLoc D.sp.cm.sig (Jst D n) v)) (hO : IsOpen O) (hx : x ∈ O) :
    ∃ γ : GRat D.sp.cm.sig (Jst D n), ratLoc D.sp.cm.sig (Jst D n) v γ ∈ O := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_skew D
  have hJ' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (δ • Jst D n) = δ • Jst D n := by
    have e1 : ∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n j i) = -Jst D n i j := by
      intro i j
      have a1 := congrFun (congrFun (jst_map D n) j) i
      have a2 := congrFun (congrFun (jst_transpose D n) i) j
      simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply] at a1 a2
      rw [a1, a2]
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [e1]
    have hδ' : (D.sp.cm.sig : D.host.E →+* D.host.E) δ = -δ := hδ
    rw [hδ', neg_mul_neg]
  have hdet' : (δ • Jst D n).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hδ0) (jst_det D n)
  have hE : Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (δ • Jst D n) =
      Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) := uj_smul _ _ (Ne.isUnit hδ0)
  have hR : HR (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n) = HR (Fv D.host.F v) D.sp.cm.sig (Jst D n) := by
    show Formalism.UG.UJ _ (JR _ _) = Formalism.UG.UJ _ (JR _ _)
    have e : JR (F := D.host.F) (Fv D.host.F v) (δ • Jst D n) =
        inclR (F := D.host.F) (Fv D.host.F v) δ • JR (F := D.host.F) (Fv D.host.F v) (Jst D n) := by
      ext i j
      simp [JR, map_mul]
    rw [e]
    exact uj_smul _ _ ((Ne.isUnit hδ0).map _)
  have hd := dense_loc D.host.F D.host.E v D.sp.cm.sig (sig_sig D) (sig_ne D) (δ • Jst D n) hJ' hdet'
  have hind := (isEmbedding_matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)).isInducing
  have hind' := (isEmbedding_matHom (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n)).isInducing
  obtain ⟨O₀, hO₀, rfl⟩ := hind.isOpen_iff.1 hO
  let x' : HA (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n) :=
    (⟨matHom _ _ _ x, by rw [hR]; exact x.2⟩ : HR (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n))
  have hU : IsOpen (matHom (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n) ⁻¹' O₀) := hind'.continuous.isOpen_preimage _ hO₀
  obtain ⟨h', h'O, h'A⟩ := hd.inter_open_nonempty _ hU ⟨x', hx⟩
  obtain ⟨γ', hγ', e⟩ := Subgroup.mem_map.1 h'A
  refine ⟨⟨γ', hE ▸ hγ'⟩, ?_⟩
  show matHom _ _ _ _ ∈ O₀
  have e2 : matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) (ratLoc D.sp.cm.sig (Jst D n) v ⟨γ', hE ▸ hγ'⟩) =
      Formalism.UG.bc (inclR (F := D.host.F) (Fv D.host.F v)) γ' := rfl
  rw [e2, e]
  exact h'O

end PositivityTheory.Rg.Rsw.L.LWa1

namespace PositivityTheory.Rg.Rsw.L

open LWa1 in
theorem wa1 : WeakApproximationFinitePlace := by
  intro D n v U hU g
  set x := proj D.sp.cm.sig (Jst D n) v g with hxdef
  let V : Subgroup (GLoc D.sp.cm.sig (Jst D n) v) := U.comap (emb D.sp.cm.sig (Jst D n) v)
  have hV : IsOpen (V : Set (GLoc D.sp.cm.sig (Jst D n) v)) := hU.preimage (continuous_emb _ _ v)
  have hO : IsOpen {y : GLoc D.sp.cm.sig (Jst D n) v | y⁻¹ * x ∈ V} :=
    hV.preimage (continuous_inv.mul continuous_const)
  obtain ⟨γ, hγ⟩ := approx_loc D n v x _ hO (by simp [V])
  set k := emb D.sp.cm.sig (Jst D n) v ((ratLoc D.sp.cm.sig (Jst D n) v γ)⁻¹ * x) with hk
  refine ⟨ratEmb D.sp.cm.sig (Jst D n) γ, ?_, (ratEmb D.sp.cm.sig (Jst D n) γ)⁻¹ * g * k⁻¹, ?_, k, hγ, ?_, by group⟩
  · show _ ∈ ratPts _ _
    rw [← range_ratEmb]
    exact ⟨γ, rfl⟩
  · rw [map_mul, map_mul, map_inv, map_inv, proj_ratEmb, hk, proj_emb_self, ← hxdef]
    group
  · rw [← range_emb]
    exact ⟨_, rfl⟩

end PositivityTheory.Rg.Rsw.L
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfInv
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LCfInv

variable {D : D7} {n : ℕ}

theorem fam_mul {H : G D n → ℝ≥0} {φ : G D n → ℂ} {u : G D n} (hH : ∀ g, H (g * u) = H g)
    (hφ : ∀ g, φ (g * u) = φ g) (s₁ z : ℂ) (g : G D n) : fam H φ s₁ z (g * u) = fam H φ s₁ z g := by
  simp only [fam, hH, hφ]

theorem eisS_mul {f : G D n → ℂ} {u : G D n} (hf : ∀ g, f (g * u) = f g) (g : G D n) :
    eisS f (g * u) = eisS f g := by
  unfold eisS GlobalTheory.Eis.cosetSum
  refine tsum_congr fun q => ?_
  simp only [GlobalTheory.Eis.term, ← mul_assoc, hf]

theorem E_mul {H : G D n → ℝ≥0} {φ : G D n → ℂ} {s₀ : ℂ} {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G D n → ℂ} {σ : ℝ}
    (hc : IsCont H φ s₀ U d E σ) {u : G D n} (hH : ∀ g, H (g * u) = H g) (hφ : ∀ g, φ (g * u) = φ g) (g : G D n) :
    ∀ z ∈ U, E z (g * u) = E z g := by
  have ah : AnalyticOnNhd ℂ (E · (g * u)) U := (hc.hol (g * u)).analyticOnNhd hc.isOpen
  have ag : AnalyticOnNhd ℂ (E · g) U := (hc.hol g).analyticOnNhd hc.isOpen
  obtain ⟨τ, hτ⟩ := hc.right.1
  have hx : ((max τ σ + 1 : ℝ) : ℂ) ∈ rightOf (max τ σ) := by simp
  have hxU : ((max τ σ + 1 : ℝ) : ℂ) ∈ U := hτ (rightOf_subset (le_max_left _ _) hx)
  have ev : (E · (g * u)) =ᶠ[𝓝 ((max τ σ + 1 : ℝ) : ℂ)] (E · g) := by
    filter_upwards [(isOpen_rightOf (max τ σ)).mem_nhds hx] with w hw
    have hw' : σ < w.re := lt_of_le_of_lt (le_max_right _ _) hw
    simp only [hc.eq w hw', eisS_mul (fam_mul hH hφ s₀ w)]
  exact fun z hz => ah.eqOn_of_preconnected_of_eventuallyEq ag hc.right.isPreconnected hxU ev hz

end PositivityTheory.Rg.Rsw.L.LCfInv

namespace PositivityTheory.Rg.Rsw.L

open LCfInv in
theorem cfInv : CfInv := by
  intro D n H s₀ φ U d E σ hc ε hε u hH hφ k g
  unfold cf
  congr 1
  refine circleIntegral.integral_congr hε.1.le fun z hz => ?_
  have hzU : z ∈ U := hε.2.1 (Metric.sphere_subset_closedBall hz)
  simp only [E_mul hc hH hφ g z hzU]

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWB
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped TensorProduct
open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU Filter

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]


variable (F E) in
abbrev bE : Module.Basis (Fin (Module.finrank F E)) F E := Module.finBasis F E

abbrev bV (v : HeightOneSpectrum (𝓞 F)) : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (bE F E)

theorem bV_apply (v : HeightOneSpectrum (𝓞 F)) (k : Fin (Module.finrank F E)) : bV (E := E) v k = 1 ⊗ₜ[F] bE F E k :=
  Algebra.TensorProduct.basis_apply _ _

theorem crd_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) (k : Fin (Module.finrank F E)) :
    (bV v).repr (a ⊗ₜ[F] e) k = a * algebraMap F (Fv F v) ((bE F E).repr e k) := by
  simp [bV, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def, mul_comm]

theorem exists_den (x : E) : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * x) := by
  have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have h2 : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  exact ⟨y, hy, by rwa [zsmul_eq_mul] at hi⟩

def den (x : E) : ℤ := Classical.choose (exists_den x)

theorem den_ne (x : E) : den x ≠ 0 := (Classical.choose_spec (exists_den x)).1

theorem den_int (x : E) : IsIntegral ℤ ((den x : E) * x) := (Classical.choose_spec (exists_den x)).2


variable (F E) in
def trM : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) F := fun i j => Algebra.trace F E (bE F E i * bE F E j)

theorem trM_det : (trM F E).det ≠ 0 := by
  have h := Algebra.discr_not_zero_of_basis F (bE F E)
  rw [Algebra.discr_def] at h
  convert h using 2
  ext i j
  simp [trM, Algebra.traceMatrix_apply, Algebra.traceForm_apply]

def IsGood (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (∀ (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (k : Fin (Module.finrank F E)),
      algebraMap F (Fv F v) ((bE F E).repr ((RingOfIntegers.basis E l : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F) ∧
    (∀ k, algebraMap F (Fv F v) ((den (bE F E k) : F))⁻¹ ∈ v.adicCompletionIntegers F) ∧
    (∀ i j, algebraMap F (Fv F v) ((trM F E)⁻¹ i j) ∈ v.adicCompletionIntegers F) ∧
    (∀ k, algebraMap F (Fv F v) (Algebra.trace F E (bE F E k)) ∈ v.adicCompletionIntegers F) ∧
    algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F

theorem eventually_int (x : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) x).2

theorem eventually_good : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, IsGood F E v :=
  (eventually_all.2 fun _ => eventually_all.2 fun _ => eventually_int _).and
    ((eventually_all.2 fun _ => eventually_int _).and
    ((eventually_all.2 fun _ => eventually_all.2 fun _ => eventually_int _).and
    ((eventually_all.2 fun _ => eventually_int _).and (eventually_int _))))

theorem eventually_coord (y : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    ∀ k, algebraMap F (Fv F v) ((bE F E).repr y k) ∈ v.adicCompletionIntegers F :=
  eventually_all.2 fun _ => eventually_int _

variable {v : HeightOneSpectrum (𝓞 F)}

theorem IsGood.half (hv : IsGood F E v) : algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F := hv.2.2.2.2

theorem IsGood.ogen (hv : IsGood F E v) (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (k : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) ((bE F E).repr ((RingOfIntegers.basis E l : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F :=
  hv.1 l k

theorem IsGood.deninv (hv : IsGood F E v) (k : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) ((den (bE F E k) : F))⁻¹ ∈ v.adicCompletionIntegers F := hv.2.1 k

theorem IsGood.trinv (hv : IsGood F E v) (i j : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) ((trM F E)⁻¹ i j) ∈ v.adicCompletionIntegers F := hv.2.2.1 i j

theorem IsGood.trb (hv : IsGood F E v) (k : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) (Algebra.trace F E (bE F E k)) ∈ v.adicCompletionIntegers F := hv.2.2.2.1 k

theorem one_tmul_b_mem (hv : IsGood F E v) (k : Fin (Module.finrank F E)) :
    (1 : Fv F v) ⊗ₜ[F] bE F E k ∈ intLoc F E v := by
  have hN : (den (bE F E k) : F) ≠ 0 := by exact_mod_cast den_ne (bE F E k)
  let o : 𝓞 E := ⟨(den (bE F E k) : E) * bE F E k, den_int (bE F E k)⟩
  have ho : (o : E) = (den (bE F E k) : E) * bE F E k := rfl
  have e : (1 : Fv F v) ⊗ₜ[F] bE F E k = algebraMap F (Fv F v) ((den (bE F E k) : F))⁻¹ ⊗ₜ[F] (o : E) := by
    rw [ho]
    have : ((den (bE F E k) : E) * bE F E k) = (den (bE F E k) : F) • bE F E k := by
      rw [Algebra.smul_def]; simp
    rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hN,
      map_one]
  rw [e]
  exact tmul_mem_intLoc (hv.deninv k) o

theorem tmul_one_mem {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) : a ⊗ₜ[F] (1 : E) ∈ intLoc F E v := by
  simpa using tmul_mem_intLoc (E := E) ha (1 : 𝓞 E)

theorem mem_intLoc_iff (hv : IsGood F E v) (z : Fv F v ⊗[F] E) :
    z ∈ intLoc F E v ↔ ∀ k, (bV v).repr z k ∈ v.adicCompletionIntegers F := by
  constructor
  · intro hz
    refine intLoc_induction (p := fun z => ∀ k, (bV v).repr z k ∈ v.adicCompletionIntegers F) (fun a ha x k => ?_)
      (fun k => by simp) (fun y z hy hz k => by rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hy k) (hz k))
      (fun y hy k => by rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hy k)) hz
    rw [crd_tmul]
    refine mul_mem ha ?_
    let L : 𝓞 E →+ F := ((Finsupp.applyAddHom k).comp (bE F E).repr.toLinearMap.toAddMonoidHom).comp
      (algebraMap (𝓞 E) E).toAddMonoidHom
    have e : L x = ∑ l, ((RingOfIntegers.basis E).repr x l) • L (RingOfIntegers.basis E l) := by
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_zsmul]
    change algebraMap F (Fv F v) (L x) ∈ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine sum_mem fun l _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (hv.ogen l k) _
  · intro h
    rw [← (bV v).sum_repr z]
    refine sum_mem fun k _ => ?_
    rw [bV_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e : (bV v).repr z k ⊗ₜ[F] bE F E k = ((bV v).repr z k ⊗ₜ[F] (1 : E)) * ((1 : Fv F v) ⊗ₜ[F] bE F E k) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    exact mul_mem (tmul_one_mem (h k)) (one_tmul_b_mem hv k)

theorem trace_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F (Fv F v) (Algebra.trace F E e) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Algebra.trace_eq_matrix_trace (bV v), Algebra.trace_eq_matrix_trace (bE F E), Matrix.trace, Matrix.trace,
    map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    bV_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, crd_tmul]

theorem trace_eq_sum (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z =
      ∑ k, (bV v).repr z k * algebraMap F (Fv F v) (Algebra.trace F E (bE F E k)) := by
  conv_lhs => rw [← (bV v).sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bV_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, trace_tmul]

theorem trace_mem (hv : IsGood F E v) {z : Fv F v ⊗[F] E} (hz : z ∈ intLoc F E v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
  rw [trace_eq_sum]
  exact sum_mem fun k _ => mul_mem (((mem_intLoc_iff hv z).1 hz) k) (hv.trb k)

theorem mem_of_trace (hv : IsGood F E v) (c : Fv F v ⊗[F] E)
    (h : ∀ t ∈ intLoc F E v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * t) ∈ v.adicCompletionIntegers F) :
    c ∈ intLoc F E v := by
  classical
  set u : Fin (Module.finrank F E) → Fv F v := fun j => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * (1 ⊗ₜ[F] bE F E j))
  have hu : ∀ j, u j ∈ v.adicCompletionIntegers F := fun j => h _ (one_tmul_b_mem hv j)
  have hu' : ∀ j, u j = ∑ l, (bV v).repr c l * algebraMap F (Fv F v) (trM F E l j) := by
    intro j
    simp only [u]
    conv_lhs => rw [← (bV v).sum_repr c]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [bV_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      trace_tmul]
    rfl
  have hT : trM F E * (trM F E)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 trM_det)
  refine (mem_intLoc_iff hv c).2 fun k => ?_
  have e : (bV v).repr c k = ∑ j, u j * algebraMap F (Fv F v) ((trM F E)⁻¹ j k) := by
    have h1 : ∀ l, ∑ j, algebraMap F (Fv F v) (trM F E l j) * algebraMap F (Fv F v) ((trM F E)⁻¹ j k) =
        if l = k then 1 else 0 := by
      intro l
      have := congrFun (congrFun hT l) k
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [← map_mul, ← map_sum, this]
      split_ifs <;> simp
    simp_rw [hu', Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, h1]
    simp
  rw [e]
  exact sum_mem fun j _ => mul_mem (hu j) (hv.trinv j k)

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

