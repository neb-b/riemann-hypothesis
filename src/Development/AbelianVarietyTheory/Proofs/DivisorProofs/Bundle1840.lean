module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepDerivativeLawOfL2Isometric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteL2ABoundWords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1751

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDeterminantOpenImage
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SkewLeviNear

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.SkewLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem continuous_atPlace : Continuous (atPlace (F := F) v) :=
  Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v)

theorem continuous_linear_prod (f : Fv F v × Fv F v →ₗ[Fv F v] Fv F v) : Continuous f := by
  have e : ∀ p : Fv F v × Fv F v, f p = p.1 * f (1, 0) + p.2 * f (0, 1) := by
    intro p
    rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add (f := _)]
    congr 1
    ext <;> simp
  have : (f : Fv F v × Fv F v → Fv F v) = fun p => p.1 * f (1, 0) + p.2 * f (0, 1) := funext e
  rw [this]
  exact (continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)

theorem continuous_tensAt_split (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) :
    Continuous fun p : Fv F v × Fv F v => tensAt E v ((splitAlgEquiv h t).symm p) := by
  let b := Module.Free.chooseBasis F E
  let bv := Algebra.TensorProduct.basis (Fv F v) b
  have key : ∀ y : TensorProduct F (Fv F v) E,
      tensAt E v y = ∑ i, atPlace v (bv.repr y i) • ((1 : AF F) ⊗ₜ[F] b i) := by
    intro y
    conv_lhs => rw [← bv.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, tensAt_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have : (fun p : Fv F v × Fv F v => tensAt E v ((splitAlgEquiv h t).symm p)) =
      fun p => ∑ i, atPlace v (bv.repr ((splitAlgEquiv h t).symm p) i) • ((1 : AF F) ⊗ₜ[F] b i) :=
    funext fun p => key _
  rw [this]
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  refine continuous_finsetSum _ fun i _ => ?_
  have hc : Continuous fun p : Fv F v × Fv F v => atPlace v (bv.repr ((splitAlgEquiv h t).symm p) i) :=
    continuous_atPlace.comp (continuous_linear_prod ((bv.coord i).comp (splitAlgEquiv h t).symm.toLinearMap))
  exact hc.smul (continuous_const : Continuous fun _ : Fv F v × Fv F v => ((1 : AF F) ⊗ₜ[F] b i : AE F E))

end GlobalTheory.SkewLeviNear

namespace GlobalTheory.SkewLeviNear

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.SkewLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem continuous_lift_locMat (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) :
    Continuous fun g : GL (Fin n) (Fv F v) => lift v (locMat h t J g) := by
  have hc : Continuous fun g : GL (Fin n) (Fv F v) => conjComp t J g :=
    (continuous_const.matrix_mul Units.continuous_coe_inv.matrix_transpose).matrix_mul continuous_const
  refine continuous_matrix fun i j => ?_
  have e : (fun g : GL (Fin n) (Fv F v) => lift v (locMat h t J g) i j) = fun g : GL (Fin n) (Fv F v) =>
      (1 : Matrix (Fin n) (Fin n) (AE F E)) i j +
        (tensAt E v ((splitAlgEquiv h t).symm ((g : Matrix (Fin n) (Fin n) (Fv F v)) i j, conjComp t J g i j)) +
          -tensAt E v ((1 : Matrix (Fin n) (Fin n) (TensorProduct F (Fv F v) E)) i j)) := by
    funext g
    simp only [lift, ext0, Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, map_sub]
    rw [sub_eq_add_neg]
    rfl
  rw [e]
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  refine continuous_const.add (Continuous.add ?_ continuous_const)
  refine (continuous_tensAt_split h t).comp (Continuous.prodMk ?_ ?_)
  · exact (Units.continuous_val.matrix_elem i j)
  · exact hc.matrix_elem i j

end GlobalTheory.SkewLeviNear

namespace GlobalTheory.SkewLeviNear

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.SkewLevi

theorem near_one_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ U ∈ 𝓝 (1 : UA σ G.W.J), ∃ V ∈ 𝓝 (1 : (Fv F v)ˣ), ∀ x ∈ V,
      ∃ h ∈ UAt σ G.W (evFin F v), h ∈ U ∧ ((mat h).map (piW t)).det = (x : Fv F v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t U hU
  have h := hTr.base.cm
  have hJ : IsUnit (G.W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hW.sig (InfinitePlace.mk φ))
    have h1 : G.W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show G.W.J.map _ = RingHom.mapMatrix _ G.W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show G.W.J.map t = (t : E →+* Fv F v).mapMatrix G.W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  let Ψ : GL (Fin (a + a')) (Fv F v) → UA σ G.W.J := fun g =>
    ⟨adelicGL h t G.W.J hJ g, lift_unitary v σ G.W.J _ (locMat_unitary_skew h t G.W.J hJ hTr.geo.hW.skew g)⟩
  have hΨc : Continuous Ψ := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨continuous_lift_locMat h t G.W.J, ?_⟩) _
    exact (continuous_lift_locMat h t G.W.J).comp continuous_inv
  have hΨ1 : Ψ 1 = 1 := Subtype.ext (Units.ext (by
    change lift v (LeviAtPlace.locMat h t G.W.J 1) = 1
    rw [locMat_one h t G.W.J hJ, lift_one]))
  have hΨt : ∀ g, (mat (Ψ g)).map (piW t) = g.1 := by
    intro g
    change (lift v (LeviAtPlace.locMat h t G.W.J g)).map (piW t) = g.1
    have key : (lift v (LeviAtPlace.locMat h t G.W.J g)).map (piW t) =
        (LeviAtPlace.locMat h t G.W.J g).map (splitProj t) := by
      conv_rhs => rw [← compFin_lift v (LeviAtPlace.locMat h t G.W.J g), Matrix.map_map]
      rfl
    rw [key]
    exact pairMat_fst h t _ _
  have i0 : Fin (a + a') := ⟨0, by have := hTr.geo.lt; omega⟩
  let D : (Fv F v)ˣ →* GL (Fin (a + a')) (Fv F v) :=
    Units.map ((Matrix.diagonalRingHom (Fin (a + a')) (Fv F v)).toMonoidHom.comp
      (MonoidHom.mulSingle (fun _ => Fv F v) i0))
  have hDv : ∀ x : (Fv F v)ˣ, ((D x : GL (Fin (a + a')) (Fv F v)) : Matrix (Fin (a + a')) (Fin (a + a')) (Fv F v)) =
      Matrix.diagonal (Pi.mulSingle i0 (x : Fv F v)) := fun x => rfl
  have hDc : Continuous D := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have : (Units.val ∘ D) = fun x : (Fv F v)ˣ => Matrix.diagonal (Pi.mulSingle i0 (x : Fv F v)) := funext hDv
      rw [this]
      exact (continuous_mulSingle i0 |>.comp Units.continuous_val).matrix_diagonal
    · have : (fun x => ((D x)⁻¹ : GL (Fin (a + a')) (Fv F v)).1) =
          fun x : (Fv F v)ˣ => Matrix.diagonal (Pi.mulSingle i0 ((x⁻¹ : (Fv F v)ˣ) : Fv F v)) := by
        funext x; rw [← map_inv]; rfl
      rw [this]
      exact (continuous_mulSingle i0 |>.comp Units.continuous_coe_inv).matrix_diagonal
  have hf : Continuous fun x => Ψ (D x) := hΨc.comp hDc
  have hf1 : Ψ (D 1) = 1 := by rw [map_one, hΨ1]
  refine ⟨(fun x => Ψ (D x)) ⁻¹' U, hf.continuousAt.preimage_mem_nhds (by rw [hf1]; exact hU), fun x hx => ?_⟩
  refine ⟨Ψ (D x), lift_sub_one_at v _, hx, ?_⟩
  rw [hΨt, hDv, Matrix.det_diagonal]
  simp

end GlobalTheory.SkewLeviNear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserLeftPreservesVacuumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_latticeStabiliser_left_preserves_vacuumType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) → Acts (evFin F v) (om (k, 1)) φ φ₁ →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₁
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ₁)) := by
  first | exact @GlobalTheory.VacTransportLeft.transport_left | exact GlobalTheory.VacTransportLeft.transport_left | (intros; apply GlobalTheory.VacTransportLeft.transport_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserRightPreservesVacuuStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_latticeStabiliser_right_preserves_vacuumType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) → Acts (evFin F v) (om (1, k)) φ φ₁ →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₁
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ₁)) := by
  first | exact @GlobalTheory.VacTransport.transport | exact GlobalTheory.VacTransport.transport | (intros; apply GlobalTheory.VacTransport.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTransportArchimedeanSliceSobolevBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

open MeasureTheory

namespace GlobalTheory.WeilL2Words

section Core

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem schA_decomp {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ (n : ℕ) (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  rw [GlobalTheory.WeilM.schA, Submodule.mem_span_set'] at hΦ
  obtain ⟨n, c, s, rfl⟩ := hΦ
  choose f g hg hfg using fun i => (s i).2
  refine ⟨n, fun i => c i • f i, g, hg, Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hfg i]
  ext a
  simp [GlobalTheory.WeilM.pureA, mul_assoc]

theorem list_sum_ne_top {l : List ENNReal} (h : ∀ a ∈ l, a ≠ ⊤) : l.sum ≠ ⊤ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons]
    exact ENNReal.add_ne_top.2 ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

variable [Invertible (2 : AdeleRing (𝓞 F) F)] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}

theorem dS_mem (hψ : IsStdInf F ψ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : dS F ψ h Φ ∈ GlobalTheory.WeilM.schA F κ := by
  obtain ⟨n, f, g, hg, rfl⟩ := schA_decomp hΦ
  obtain ⟨f', hf'⟩ := _root_.GlobalTheory.WeilL2Words.dS_sum_pureA F κ ψ hψ n g f h
  rw [hf']
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, g i, hg i, rfl⟩

theorem word_mem (hψ : IsStdInf F ψ) : ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ},
    Φ ∈ GlobalTheory.WeilM.schA F κ → word F ψ w Φ ∈ GlobalTheory.WeilM.schA F κ
  | [], _, hΦ => hΦ
  | h :: w, _, hΦ => by
    rw [word_cons]
    exact dS_mem hψ h (word_mem hψ w hΦ)

theorem word_sum (hψ : IsStdInf F ψ) {m : ℕ} (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ), ∃ f' : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      word F ψ w (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by
  intro w f
  induction w with
  | nil => exact ⟨f, rfl⟩
  | cons h w ih =>
    obtain ⟨f1, e1⟩ := ih
    obtain ⟨f2, e2⟩ := _root_.GlobalTheory.WeilL2Words.dS_sum_pureA F κ ψ hψ m g f1 h
    exact ⟨f2, by rw [word_cons, e1, e2]⟩

theorem word_law (hψ : IsStdInf F ψ) {G : Type} [Group G] (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ))
    (pres : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ)
    (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (himpl : ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      om p (GlobalTheory.WeilM.schr ψ (archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (archPair F h) (om p φ))
    (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (hiso : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, l2A F μ (om p φ) = l2A F μ φ) (p : G) :
    ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) {φ : (κ → AdeleRing (𝓞 F) F) → ℂ}, φ ∈ GlobalTheory.WeilM.schA F κ →
      word F ψ w (om p φ) = om p (word F ψ (w.map (M p)) φ)
  | [], _, _ => rfl
  | h :: w, φ, hφ => by
    rw [List.map_cons, word_cons, word_cons, word_law hψ om pres M himpl μ hμ hiso p w hφ]
    exact _root_.GlobalTheory.WeilL2Words.dS_om_eq F κ ψ hψ om pres M himpl μ hμ hiso p h _ (word_mem hψ _ hφ)

theorem slice_l2_of (hψ : IsStdInf F ψ) {G : Type} [Group G] [TopologicalSpace G]
    (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ))
    (pres : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ)
    (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (himpl : ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      om p (GlobalTheory.WeilM.schr ψ (archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (archPair F h) (om p φ))
    (hM : ∀ h, Continuous fun p => M p h)
    (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (hiso : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, l2A F μ (om p φ) = l2A F μ φ)
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (p0 : G)
    (hfin : ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F)),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (yy j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, om p Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
    (y : (κ → FiniteAdeleRing (𝓞 F) F)) (i j : ℕ) :
    ∃ B : ℝ, ∀ᶠ p in nhds p0,
      ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2 ≤ B := by
  obtain ⟨L, C, hL⟩ := _root_.GlobalTheory.WeilL2Words.adelic_schwartz_slice_l2_word_bound F κ ψ hψ i j
  obtain ⟨N, hN, m, g, yy, hg, hdual, hf⟩ := hfin
  obtain ⟨CG, hCG, hG⟩ := GlobalTheory.T.finite_adelic_dual_basis_integral F κ m g yy hg hdual μ hμ y
  set R : ℝ := ∑ h ∈ L.flatten.toFinset, (‖M p0 h‖ + 1) with hR
  have hev : ∀ᶠ p in nhds p0, ∀ h ∈ L.flatten.toFinset, ‖M p h‖ ≤ R := by
    refine (Filter.eventually_all_finset _).2 fun h hh => ?_
    have hc : ContinuousAt (fun p => ‖M p h‖) p0 := ((hM h).norm).continuousAt
    filter_upwards [hc.eventually_lt continuousAt_const (lt_add_one ‖M p0 h‖)] with p hp
    exact hp.le.trans (Finset.single_le_sum (f := fun h => ‖M p0 h‖ + 1) (fun _ _ => by positivity) hh)
  have hB : ∀ w ∈ L, ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ ws : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ws.length = w.length →
      (∀ h ∈ ws, ‖h‖ ≤ R) → l2A F μ (word F ψ ws Φ) ≤ B :=
    fun w _ => _root_.GlobalTheory.WeilL2Words.l2A_word_le F κ ψ hψ Φ hΦ μ hμ w.length R
  choose! B hBtop hBle using hB
  have htop : ENNReal.ofReal C * (L.map fun w => CG * B w).sum ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (list_sum_ne_top fun a ha => ?_)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    exact ENNReal.mul_ne_top hCG (hBtop w hw)
  refine ⟨(ENNReal.ofReal C * (L.map fun w => CG * B w).sum).toReal, ?_⟩
  filter_upwards [hev, hN] with p hp hpN
  have key := hL (om p Φ) (pres p Φ hΦ) y
  have hsum : (L.map fun w => ∫⁻ x, ‖word F ψ w (om p Φ) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum ≤
      (L.map fun w => CG * B w).sum := by
    refine List.sum_le_sum fun w hw => ?_
    obtain ⟨f, hfp⟩ := hf p hpN
    obtain ⟨f', hf'⟩ := word_sum hψ g w f
    have e1 : word F ψ w (om p Φ) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by rw [hfp, hf']
    calc ∫⁻ x, ‖word F ψ w (om p Φ) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2
        ≤ CG * l2A F μ (word F ψ w (om p Φ)) := by rw [e1]; exact hG f'
      _ = CG * l2A F μ (word F ψ (w.map (M p)) Φ) := by
          rw [word_law hψ om pres M himpl μ hμ hiso p w hΦ, hiso p _ (word_mem hψ _ hΦ)]
      _ ≤ CG * B w := by
          gcongr
          refine hBle w hw _ (List.length_map _) fun h hh => ?_
          obtain ⟨h0, h0m, rfl⟩ := List.mem_map.1 hh
          exact hp h0 (List.mem_toFinset.2 (List.mem_flatten.2 ⟨w, hw, h0m⟩))
  exact (ENNReal.ofReal_le_iff_le_toReal htop).1 (key.trans (by gcongr))

end Core

end GlobalTheory.WeilL2Words

theorem GlobalTheory.WeilL2Words.weilTransport_archimedeanSlice_sobolev_bounds_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (y : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) p0 (i j : ℕ), ∃ B : ℝ,
      ∀ᶠ p in nhds p0, ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F x y)) x‖) ^ 2 ≤ B := by
  intro D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ _ co hco ω hω om hom Φ hΦ y p0 i j
  have hI := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom
  obtain ⟨M, himpl, hM⟩ := _root_.GlobalTheory.ArchTransportHost.archDir_transport_host D ψ _ _ JA JB ξ κ co om hI.2
  obtain ⟨μ, hμ, hiso⟩ := _root_.GlobalTheory.WeilL2Transport.l2A_transport D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom
  exact GlobalTheory.WeilL2Words.slice_l2_of (_root_.GlobalTheory.WeilL2Words.StdTheta.isStdInf_of_isStdChar D ψ hψ) om hI.1 M himpl hM μ hμ hiso hΦ p0
    (_root_.GlobalTheory.WeilCont.exists_local_finite_parts D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom Φ hΦ p0) y i j
end
end

