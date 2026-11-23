module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitCentreDerivativeEqSumDiagonalMatrixUnits
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.CuspRep.ZcTrace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def conjPerm : Equiv.Perm (E →+* ℂ) where
  toFun := ComplexEmbedding.conjugate
  invFun := ComplexEmbedding.conjugate
  left_inv τ := by ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  right_inv τ := by ext x; simp [ComplexEmbedding.conjugate_coe_eq]

theorem sum_atEmb_I : ∑ τ : E →+* ℂ, atEmb τ Complex.I = 0 := by
  have e : ∀ τ : E →+* ℂ, atEmb (conjPerm τ) Complex.I = -atEmb τ Complex.I := by
    intro τ
    change atEmb (ComplexEmbedding.conjugate τ) Complex.I = _
    rw [atEmb_conj, Complex.conj_I, atEmb_eq]; simp
  have h := Equiv.sum_comp (conjPerm (E := E)) (fun τ => atEmb τ Complex.I)
  simp only [e, Finset.sum_neg_distrib] at h
  have h2 : (2 : ℝ) • ∑ τ : E →+* ℂ, atEmb τ Complex.I = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h]; simp
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem sum_atEmb_one : ∑ τ : E →+* ℂ, atEmb τ 1 = (2 : ℝ) • (1 : Cinf E) := by
  classical
  have e : ∀ τ : E →+* ℂ, atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1 := by
    intro τ; unfold atEmb; split_ifs <;> simp
  simp only [e]
  funext w
  rw [Finset.sum_apply]
  simp only [Pi.single_apply, Finset.sum_boole]
  have hc : (Finset.univ.filter fun τ : E →+* ℂ => w = InfinitePlace.mk τ).card = 2 := by
    have := InfinitePlace.card_filter_mk_eq w
    rw [InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩] at this
    rw [← this]; congr 1; ext τ; simp [eq_comm]
  rw [hc]
  simp

theorem sum_Eop (a : ℕ) (i : Fin a) : ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Eop, ← Finset.smul_sum, Finset.sum_sub_distrib, ← map_sum, sum_atEmb_I, sum_atEmb_one, map_zero,
    smul_zero, sub_zero, map_smul]
  rw [← Complex.coe_smul, smul_smul]
  norm_num

end GlobalTheory.CuspRep.ZcTrace

namespace GlobalTheory.ResW


open GlobalTheory.CuspRep.ZcTrace in
theorem zc_eq_sum_Eop : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), GlobalTheory.ResW.zc E a = ∑ τ : E →+* ℂ, ∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i := by
  intro E _ _ _ a
  rw [Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sum_Eop, lieS_apply, ← map_sum]
  unfold zc
  congr 1
  funext k l
  simp [toL, Finset.sum_apply, Matrix.single_apply, eq_comm]
  simp only [Finset.sum_apply, Pi.single_apply]
  by_cases h : k = l
  · subst h; simp [ite_apply, Pi.single_apply]
  · simp [ite_apply, Pi.single_apply, h, Ne.symm h]

end GlobalTheory.ResW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterLawsNormOneIdelesOfKernelChain
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.Forms

noncomputable section

namespace GlobalTheory.TwV.MuLawPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem generalLinearGroupOne_eq_of_det_eq {R : Type} [CommRing R] {g h : GL (Fin 1) R}
    (e : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h) : g = h := by
  have e' : ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) = ((Matrix.GeneralLinearGroup.det h : Rˣ) : R) := by rw [e]
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one] at e'
  ext a b
  fin_cases a; fin_cases b
  exact e'

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def gl1 (x : (AfE F E)ˣ) : GL (Fin 1) (AfE F E) :=
  Units.map (Matrix.scalar (Fin 1) : AfE F E →+* Matrix (Fin 1) (Fin 1) (AfE F E)).toMonoidHom x

theorem det_ideleAsGL1 (x : (AfE F E)ˣ) : Matrix.GeneralLinearGroup.det (gl1 x) = x := by
  ext
  simp [gl1, Matrix.GeneralLinearGroup.val_det_apply]

theorem ideleAsGL1_mem_unitary_of_normOne (σ : E →ₐ[F] E) {x : (AfE F E)ˣ} (hx : x ∈ U1 σ) :
    gl1 x ∈ UPts σ (1 : Matrix (Fin 1) (Fin 1) E) (FiniteAdeleRing (𝓞 F) F) := by
  have h1 : (x : AfE F E) * sigR σ (FiniteAdeleRing (𝓞 F) F) (x : AfE F E) = 1 := by
    have := congrArg (fun u : (AfE F E)ˣ => (u : AfE F E)) (MonoidHom.mem_ker.1 hx)
    simpa [conjId] using this
  show cT _ _ * _ * _ = _
  ext a b
  fin_cases a; fin_cases b
  simp [cT, gl1, Matrix.mul_apply, inclE]
  rw [← Algebra.TensorProduct.one_def, mul_one, mul_comm]; exact h1

end Gen

section D
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}
  (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt)

theorem muOf_det (j : ℕ) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    muOf t u μ dtU j (Matrix.GeneralLinearGroup.det y.1) = (((t.O u μ).mt j (dtU y) : ℂˣ) : ℂ) := by
  have h : ∃ y' : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y'.1 = Matrix.GeneralLinearGroup.det y.1 := ⟨y, rfl⟩
  unfold muOf
  rw [dite_eq_left h]
  have e : h.choose = y := Subtype.ext (generalLinearGroupOne_eq_of_det_eq h.choose_spec)
  rw [e]

theorem exists_unitaryOne_det_eq_normOneIdele {x : (AfE D.host.F D.host.E)ˣ} (hx : x ∈ U1 (sigD D)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x :=
  ⟨⟨gl1 x, ideleAsGL1_mem_unitary_of_normOne _ hx⟩, det_ideleAsGL1 x⟩

end D

section D2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}
  (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt)


set_option maxHeartbeats 4000000 in
theorem muOf_det_mul (j : ℕ) (x y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    muOf t u μ dtU j (Matrix.GeneralLinearGroup.det x.1 * Matrix.GeneralLinearGroup.det y.1) =
      muOf t u μ dtU j (Matrix.GeneralLinearGroup.det x.1) * muOf t u μ dtU j (Matrix.GeneralLinearGroup.det y.1) := by
  have e : Matrix.GeneralLinearGroup.det x.1 * Matrix.GeneralLinearGroup.det y.1 =
      Matrix.GeneralLinearGroup.det (x * y).1 := by
    rw [Subgroup.coe_mul, map_mul]
  have h2 : dtU (x * y) = dtU x * dtU y := dtU.map_mul x y
  have h3 : (t.O u μ).mt j (dtU x * dtU y) = (t.O u μ).mt j (dtU x) * (t.O u μ).mt j (dtU y) :=
    ((t.O u μ).mt j).map_mul _ _
  have k1 := muOf_det (t := t) (u := u) (μ := μ) dtU j (x * y)
  rw [h2, h3, Units.val_mul, ← e] at k1
  rw [k1, muOf_det, muOf_det]

end D2

theorem rationalIdele_mem_normOne_of_norm_eq_one {D : D7} (z : D.host.Eˣ) (hz : (z : D.host.E) * D.host.conj (z : D.host.E) = 1) :
    ratId D.host.F D.host.E z ∈ U1 (sigD D) := by
  have hs : (sigD D : D.host.E →+* D.host.E) (z : D.host.E) = D.host.conj (z : D.host.E) := Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
  rw [U1, MonoidHom.mem_ker]
  ext
  simp only [MonoidHom.mul_apply, MonoidHom.id_apply, conjId, ratId, Units.val_mul, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one]
  show inclE _ (z : D.host.E) * sigR (sigD D) _ (inclE _ (z : D.host.E)) = 1
  simp only [inclE, sigR, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [show (sigD D) (z : D.host.E) = D.host.conj (z : D.host.E) from hs, hz, Algebra.TensorProduct.one_def]

theorem muLaw_underTie : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hT'
  have hA := GlobalTheory.T.kernelChainCharacters_algebraic_unitaryPoints A dtU a hP hT'
  have hU := GlobalTheory.T.kernelStepCharacter_eq_one_integralUnitary A dtU a hP hT'
  have hR := GlobalTheory.T.kernelChainCharacter_normOne_eq_infinityType A dtU a hP hT'
  intro i hi
  refine ⟨fun y => muOf_det dtU (i + 1) y, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · have h1 := muOf_det (t := t) (u := u) (μ := μ) dtU (i + 1) 1
    simp only [OneMemClass.coe_one, map_one, Units.val_one] at h1
    exact h1
  · intro x hx y hy
    obtain ⟨x', rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    obtain ⟨y', rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hy
    exact muOf_det_mul dtU (i + 1) x' y'
  · intro x hx
    obtain ⟨y, rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    rw [muOf_det]
    exact hA i hi y
  · intro x hx hint hv
    obtain ⟨y, rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    rw [muOf_det, hU i hi y hint hv, Units.val_one]
  · obtain ⟨e, he, hz⟩ := hR i hi
    refine ⟨e, he, fun z hz1 => ?_⟩
    obtain ⟨y, hy⟩ := exists_unitaryOne_det_eq_normOneIdele (rationalIdele_mem_normOne_of_norm_eq_one z hz1)
    rw [← hy, muOf_det]
    exact hz z hz1 y hy

end GlobalTheory.TwV.MuLawPf
end
end

