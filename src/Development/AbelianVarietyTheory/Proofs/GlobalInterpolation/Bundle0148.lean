module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0146
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelEqPointKernelAtRepresentatives
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitVectorPerpAllIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasComplementOfBasis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AutFormDefiniteUnitaryEqSumPolynomialMulAutForm
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryDecomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev infSpan (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

theorem RU_RU (x y : UA E n) (φ : UA E n → ℂ) : RU E n x (RU E n y φ) = RU E n (x * y) φ := by
  rw [map_mul]; rfl

theorem mem_infSpan (φ : UA E n → ℂ) (k : infU E n) : RU E n k φ ∈ infSpan φ :=
  Submodule.subset_span ⟨k, rfl⟩

theorem infSpan_stable (φ : UA E n → ℂ) (k : infU E n) : ∀ ψ ∈ infSpan φ, RU E n k ψ ∈ infSpan φ := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨l, rfl⟩ := h
    rw [RU_RU]
    exact mem_infSpan φ (k * l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h₁ h₂ => rw [map_add (f := _)]; exact Submodule.add_mem _ h₁ h₂
  | smul c _ _ h => rw [map_smul]; exact Submodule.smul_mem _ c h

def finStab (φ : UA E n → ℂ) : Subgroup (finU (E := E) (n := n)) where
  carrier := {k | RU E n k φ = φ}
  one_mem' := by
    change RU E n 1 φ = φ
    rw [map_one]; rfl
  mul_mem' := fun {a b} ha hb => by
    change RU E n (a.1 * b.1) φ = φ
    rw [← RU_RU, show RU E n b φ = φ from hb]
    exact ha
  inv_mem' := fun {a} ha => by
    change RU E n (a.1)⁻¹ φ = φ
    conv_lhs => rw [← show RU E n a φ = φ from ha]
    rw [RU_RU, inv_mul_cancel, map_one]; rfl

theorem isAutFormU_of_mem (hc : ∀ k : infU E n, ∀ g ∈ finU (E := E) (n := n), k.1 * g = g * k.1) {φ : UA E n → ℂ}
    (hφ : IsAutFormU φ) (ψ : UA E n → ℂ) (hψ : ψ ∈ infSpan φ) : IsAutFormU ψ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · induction hψ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      exact hφ.cont.comp (continuous_mul_const l.1)
    | zero => exact continuous_const
    | add _ _ _ _ h₁ h₂ => exact h₁.add h₂
    | smul c _ _ h => exact h.const_smul c
  · intro γ hγ g
    induction hψ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      change φ (γ * g * l) = φ (g * l)
      rw [mul_assoc, hφ.left γ hγ]
    | zero => rfl
    | add _ _ _ _ h₁ h₂ => simp only [Pi.add_apply, h₁, h₂]
    | smul c _ _ h => simp only [Pi.smul_apply, h]
  · refine Subgroup.isOpen_mono (H₁ := finStab φ) (H₂ := finStab ψ) (fun k hk => ?_) hφ.level
    change RU E n k ψ = ψ
    induction hψ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      rw [RU_RU, ← hc l k.1 k.2, ← RU_RU, show RU E n k φ = φ from hk]
    | zero => rw [map_zero]
    | add _ _ _ _ h₁ h₂ => rw [map_add (f := _), h₁, h₂]
    | smul c _ _ h => rw [map_smul, h]
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := infSpan φ) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact infSpan_stable φ k ψ hψ

def coeff (φ : UA E n → ℂ) (l : infSpan φ →ₗ[ℂ] ℂ) : infSpan φ →ₗ[ℂ] (infU E n → ℂ) :=
  LinearMap.pi fun k => l.comp ((RU E n k).restrict (infSpan_stable φ k))

theorem continuous_coeff {φ : UA E n → ℂ} (hφ : IsAutFormU φ) (l : infSpan φ →ₗ[ℂ] ℂ) :
    Continuous fun k : infU E n => l ⟨RU E n k φ, mem_infSpan φ k⟩ := by
  have := hφ.kfin
  refine l.continuous_of_finiteDimensional.comp (Continuous.subtype_mk (continuous_pi fun g => ?_) _)
  exact hφ.cont.comp (continuous_const.mul continuous_subtype_val)

theorem finite_coeff {φ : UA E n → ℂ} (hφ : IsAutFormU φ) (l : infSpan φ →ₗ[ℂ] ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => fun x : infU E n =>
      l ⟨RU E n (x * k : infU E n) φ, mem_infSpan φ (x * k)⟩)) := by
  have := hφ.kfin
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (coeff φ l)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  refine ⟨⟨_, mem_infSpan φ k⟩, funext fun x => congrArg l (Subtype.ext ?_)⟩
  exact RU_RU x.1 k.1 φ

theorem exists_poly_mul_autForm (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ)
    (hφ : IsAutFormU φ) : ∃ (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → UA E n → ℂ),
      (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}
        ∧ IsAutFormU (e i)) ∧ ∀ (k : infU E n) (g : UA E n), φ (g * k) = ∑ i, p i k * e i g := by
  have := hφ.kfin
  let b := Module.finBasis ℂ (infSpan φ)
  refine ⟨_, fun i k => b.coord i ⟨RU E n k φ, mem_infSpan φ k⟩, fun i => (b i).1, fun i => ⟨?_, ?_⟩, fun k g => ?_⟩
  · exact GlobalTheory.UnitaryBC.rightFinite_mem_poly E n _ (continuous_coeff hφ _) (finite_coeff hφ _)
  · exact isAutFormU_of_mem (GlobalTheory.UnitarySplit.dense_and_split E n).2.2.1 hφ _ (b i).2
  · have h := congrArg (fun v : infSpan φ => v.1 g) (b.sum_repr ⟨RU E n k φ, mem_infSpan φ k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm

end GlobalTheory.UnitaryDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplitStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), Dense ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) ∧ Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} ∧ (∀ k : infU E n, ∀ g ∈ finU (E := E) (n := n), k.1 * g = g * k.1) ∧ ∃ (a : UA E n →* finU (E := E) (n := n)) (b : UA E n →* infU E n), Continuous a ∧ Continuous b ∧ (∀ x, x = (a x).1 * (b x).1) ∧ ∀ (g : finU (E := E) (n := n)) (k : infU E n), a (g.1 * k.1) = g ∧ b (g.1 * k.1) = k := by
  first | exact @GlobalTheory.UnitarySplit.dense_and_split | exact GlobalTheory.UnitarySplit.dense_and_split | (intros; apply GlobalTheory.UnitarySplit.dense_and_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetNeZeroOfHasSignature
section
noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.LandherrSignature

theorem det_ne_zero_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature A p q) : A.det ≠ 0 := by
  obtain ⟨e, P, hP⟩ := h
  intro h0
  have h1 := congrArg det hP
  rw [det_mul, det_mul, det_reindex_self, h0, mul_zero, zero_mul, Formalism.UG.Jpq, det_fromBlocks_zero₂₁, det_neg] at h1
  simp at h1
  exact pow_ne_zero q (neg_ne_zero.2 one_ne_zero) h1.symm

theorem congr_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ} {p q : ℕ}
    (hA : Formalism.UG.HasSignature A p q) (hB : Formalism.UG.HasSignature B p q) :
    ∃ Q : Matrix n n ℂ, Q.det ≠ 0 ∧ Qᴴ * A * Q = B := by
  obtain ⟨e, -⟩ := id hA
  have key : ∀ C : Matrix n n ℂ, Formalism.UG.HasSignature C p q →
      ∃ R : Matrix n n ℂ, R.det ≠ 0 ∧ Rᴴ * C * R = (Formalism.UG.Jpq p q).submatrix e e := by
    rintro C ⟨e', P, hP⟩
    have hP' : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * C.submatrix e'.symm e'.symm *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hP
    refine ⟨P.val.submatrix e' e, ?_, ?_⟩
    · refine IsUnit.ne_zero (isUnit_det_of_right_inverse (B := P.inv.submatrix e e') ?_)
      rw [submatrix_mul_equiv, P.val_inv, submatrix_one_equiv]
    · have : C = (C.submatrix e'.symm e'.symm).submatrix e' e' := by simp
      rw [this, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hP']
  obtain ⟨R, hR, h1⟩ := key A hA
  obtain ⟨S, hS, h2⟩ := key B hB
  have hu : IsUnit S.det := hS.isUnit
  refine ⟨R * S⁻¹, ?_, ?_⟩
  · rw [det_mul]
    exact mul_ne_zero hR (isUnit_nonsing_inv_det _ hu).ne_zero
  · calc (R * S⁻¹)ᴴ * A * (R * S⁻¹) = S⁻¹ᴴ * (Rᴴ * A * R) * S⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (S * S⁻¹)ᴴ * B * (S * S⁻¹) := by
          rw [h1, ← h2]
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = B := by rw [mul_nonsing_inv _ hu]; simp

theorem form_eq {E V n : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V] [Fintype n]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (b : Module.Basis n E V) (x y : n → E) :
    h (b.equivFun.symm x) (b.equivFun.symm y) = star x ⬝ᵥ ((Matrix.of fun i j => h (b i) (b j)) *ᵥ y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply, dotProduct, mulVec, Matrix.of_apply,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem congr_of_det_norm {n : ℕ} (G G' : Matrix (Fin n) (Fin n) E) (hG : Gᴴ = G) (hG' : G'ᴴ = G')
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) (hn : ∃ z : E, G.det = z * star z * G'.det)
    (hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ Qᴴ * G.map τ * Q = G'.map τ) :
    ∃ P : Matrix (Fin n) (Fin n) E, P.det ≠ 0 ∧ Pᴴ * G * P = G' := by
  obtain ⟨z, hz⟩ := hn
  obtain ⟨P, hP, h⟩ := GlobalTheory.QNorm.landherr_and_landherrSt.1 E n G G'
    (fun a b => congrFun (congrFun hG b) a) (fun a b => congrFun (congrFun hG' b) a) hd hd'
    (fun τ => by
      obtain ⟨Q, hQ, h⟩ := hs τ
      refine ⟨Q.map (starRingEnd ℂ), ?_, ?_⟩
      · have : (Q.map (starRingEnd ℂ)).det = starRingEnd ℂ Q.det := (RingHom.map_det (starRingEnd ℂ) Q).symm
        rw [this]
        exact (map_ne_zero _).mpr hQ
      · rw [← h]
        congr 1
        ext a b
        simp)
    ⟨z, by rw [div_eq_iff hd']; exact hz⟩
  refine ⟨P.map ReciprocityTheory.ChartRestriction.G.FD.cc, ?_, ?_⟩
  · rw [GlobalTheory.Published.det_map_cc]
    exact GlobalTheory.Published.cc_ne_zero hP
  · rw [h]
    congr 2
    ext a b
    exact star_star (P b a)

theorem exists_isometry (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W₁ W₂ : HSpace E) (h₁ : W₁.SigOK) (h₂ : W₂.SigOK)
    (hr : W₁.rank = W₂.rank) (hs : ∀ τ, W₁.sig τ = W₂.sig τ) :
    ∃ φ : W₁.V ≃ₗ[E] W₂.V, ∀ x y, W₂.hT (φ x) (φ y) = W₁.hT x y := by
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.SelfDualDet.det_eq_norm_mul E hc W₁ W₂ h₁ h₂ hr hs
  let c : Fin W₁.rank ≃ Fin W₂.rank := finCongr hr
  have hH : ∀ W : HSpace E, W.gramᴴ = W.gram := fun W => by
    ext a b
    exact W.herm.eq _ _
  have hd : ∀ W : HSpace E, W.SigOK → W.gram.det ≠ 0 := fun W hW h0 => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine det_ne_zero_of_hasSignature (hW τ) ?_
    have : (W.gram.map τ).det = τ W.gram.det := (RingHom.map_det τ W.gram).symm
    rw [this, h0, map_zero]
  obtain ⟨P, hP0, hP⟩ := congr_of_det_norm (W₂.gram.submatrix c c) W₁.gram
    (by rw [conjTranspose_submatrix, hH]) (hH W₁) (by rw [det_submatrix_equiv_self]; exact hd W₂ h₂) (hd W₁ h₁)
    ⟨z, by rw [det_submatrix_equiv_self]; exact hz⟩
    (fun τ => by
      refine congr_of_hasSignature ?_ (h₁ τ)
      rw [hs τ]
      obtain ⟨e, Q, hQ⟩ := h₂ τ
      refine ⟨c.trans e, Q, ?_⟩
      rw [← hQ]
      congr 2)
  let b₂ := W₂.frame.reindex c.symm
  have e₂ : (Matrix.of fun i j => W₂.hT (b₂ i) (b₂ j)) = W₂.gram.submatrix c c := by
    ext i j
    simp [b₂, HSpace.gram]
  refine ⟨(W₁.frame.equivFun.trans (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit))).trans
    b₂.equivFun.symm, fun x y => ?_⟩
  obtain ⟨u, rfl⟩ := W₁.frame.equivFun.symm.surjective x
  obtain ⟨v, rfl⟩ := W₁.frame.equivFun.symm.surjective y
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [form_eq, form_eq, e₂]
  change star (P *ᵥ u) ⬝ᵥ (_ *ᵥ (P *ᵥ v)) = star u ⬝ᵥ (W₁.gram *ᵥ v)
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hP]

end CM

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isometry_host : ∀ (D : D7) (W₁ W₂ : HSpace D.host.E), W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank →
    (∀ τ, W₁.sig τ = W₂.sig τ) →
    ∃ φ : W₁.V ≃ₗ[D.host.E] W₂.V, ∀ x y, W₂.hT (φ x) (φ y) = W₁.hT x y := fun D =>
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W₁ W₂ => exists_isometry (E := D.host.E) D.sp.cm.cmUnram W₁ W₂

end GlobalTheory.LandherrSignature
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralCoordinatesTwistedTrueChain
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co

theorem pendTw_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l))
    (l0 : TC.Law0 I l) (u : B.Word) (a : I.ι), ∃ P : GlobalTheory.PerQ.PendTw (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (TC.tw I l l0 Z) u a, ∀ τ,
      P.br τ = brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u τ)
        (Formalism.MainNotions.product_first_zeroth_parts.sgTr (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u τ) := by
  intro B X I hI l Z l0 u a
  exact ⟨{ br := fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ)
              (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ)
           coM := fun w c => coM I u a w c
           coP := fun w => coP I u a w
           Pt_eq := _root_.GlobalTheory.PerQ.Co.coP_PtT_eq_blk I hI l Z l0 u a
           lat_co := _root_.GlobalTheory.PerQ.Co.latCo_mem_intSpan I hI l Z l0 u a
           pt_co := fun w z hz => ⟨_root_.GlobalTheory.PtIntCoord.coP_mem_intSpan I hI l Z l0 u a w z hz, _root_.GlobalTheory.PerQ.Co.PtInt.exists_mem_SP_of_coP_mem I hI l Z l0 u a w z hz⟩ }, fun _ => rfl⟩

end GlobalTheory.PerQ.Co
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelEqPointKernelAtRepresentativesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

open _root_.Formalism.L2.Col

attribute [local instance] GlobalTheory.Mem.Col2.starE

local instance representativeDatNumberField {B : Base} {X : PreX B.toPre} (I : TC B X)
    (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    @NumberField (dat I l Z u a).E (dat I l Z u a).fE :=
  (dat I l Z u a).nE

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChainKernel_eq_pointKernel_at_representatives : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).VecP I.chi → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ c c' F, (dat I l Z u a).ch.C.Kmap i c c' ((dat I l Z u a).ev i F) = (dat I l Z u a).ev (i + 1) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i c.1 c'.1 (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c') F) := by
  intro B X I h hJ l Z hv u a i hi c c' F
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := KMap.laHyp_of_vecP I (I.cols l) Z.W Z.V Z.S Z.N Z.G h hv a u i (i + 1)
  have h0 : I.A.AA ≠ ⊥ := by
    rw [I.A_AA, Ne, FractionalIdeal.coeToSubmodule_eq_bot]
    refine inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 fun h0 => ?_)
    have h1 := B.host.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at h1
    exact (differentIdeal_ne_bot : differentIdeal (𝓞 B.host.K) (𝓞 B.host.E) ≠ ⊥) h1
  have hJa : GlobalTheory.KerT.JetsAll (Pr := B.primes X) B.wts I.sel (I.tup a) (I.cst a) I.A u i (i + 1) := fun L L' hL hL' =>
    (GlobalTheory.MoveCompare.jetsIn_iff _ _ _ _ _ _ _ (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi) L L').2
      (GlobalTheory.MoveCompare.jetsAll_of_deg _ _ _ _ _ (hJ a u i hi) (GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u) hL hL')
  have hr := KMap.rhoIs I h a u hi
  refine KMap.kmap_of_jet (I.chIn u a) I.A.σ₀ (l.ch u a) (B.hcW u) hi c c' F _ ?_
  have hV := GlobalTheory.GO.ChSrc.jetInVV_trueWt (X := B.fields) (B.hcW u) hi
  have hnu : GlobalTheory.GO.ChSrc.nuEnd (B.hcW u) i = nuLast (Pr := B.primes X) B.wts u i := GlobalTheory.GO.ChSrc.nuEnd_eq (Pr := B.primes X) B.wts u hi
  rw [hnu] at hV ⊢

  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) := pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB := GlobalTheory.MoveCompare.cBof_pos hPr I.sel (I.tup a) (I.cst a) u
  have hLa' : I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (Sall (Pr := B.primes X) I.sel (I.tup a) u) := hLa
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i
    hX hPr h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) hi ⟨_, _, _, _, h.ch_tied⟩ c.1 c'.1
  have key := fun (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)) =>
    KMap.map_kerOf (X := B.fields) I.A (Sall (Pr := B.primes X) I.sel (I.tup a) u) (rowSG (B.primes X) I.sel (I.tup a)) hA hB I.sel
      (mUof (R := B.R) I.Ch (I.tup a) i) (muAtT (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i) (B.wts.lamTrue u i) (B.wts.lamTrue u (i + 1))
      (nuLast (Pr := B.primes X) B.wts u i) hV hLa' h0 hE
      (frsF I.sel (I.tup a) p.1.1) (frsF I.sel (I.tup a) p'.1.1)
      ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
      (hJa _ _ ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩) (hbox p p') F
  refine (key (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c')).trans ?_
  rw [← hr c.1 (((dat I l Z u a).I.S i).rep c) c'.1 (((dat I l Z u a).I.S (i + 1)).rep c'), ColIn.A_cD]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelsBoundConjugatePrimePlacesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChainKernels_bound_conjugatePrimePlaces : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerBar (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  first | exact @GlobalTheory.LvT.Built.TrueLaws.kerBar | exact GlobalTheory.LvT.Built.TrueLaws.kerBar | (intros; apply GlobalTheory.LvT.Built.TrueLaws.kerBar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelsBoundLevelPrimePlacesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChainKernels_bound_levelPrimePlaces : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerP (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  exact @GlobalTheory.LvT.Built.TrueLaws.kerP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitVectorPerp
section
namespace GlobalTheory.UnitPerpObj

theorem unitVectorPerp (D : Formalism.BasicNotions.D7) : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeComplements.UnitVectorPerp D :=
  (GlobalTheory.UnitVectorPerpCompare.unitVectorPerp_iff D).1 (GlobalTheory.UnitPerp.unitVectorPerp D)

end GlobalTheory.UnitPerpObj
end

