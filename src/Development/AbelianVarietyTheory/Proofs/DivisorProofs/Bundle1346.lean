module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalSetConjFiniteIndexSubgroup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblSchr

open Matrix

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    GlobalTheory.WeilM.hTens c JA (GlobalTheory.WeilM.dbl JB) x y =
      GlobalTheory.WeilM.hTens c JA JB x.toCols₁ y.toCols₁ - GlobalTheory.WeilM.hTens c JA JB x.toCols₂ y.toCols₂ := by
  unfold GlobalTheory.WeilM.hTens GlobalTheory.WeilM.dbl
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.toCols₁_apply, Matrix.toCols₂_apply, Matrix.zero_apply, Matrix.neg_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, sub_eq_add_neg]

theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    GlobalTheory.WeilM.symp c ξ JA (GlobalTheory.WeilM.dbl JB) x y =
      GlobalTheory.WeilM.symp c ξ JA JB x.toCols₁ y.toCols₁ - GlobalTheory.WeilM.symp c ξ JA JB x.toCols₂ y.toCols₂ := by
  unfold GlobalTheory.WeilM.symp
  rw [hTens_dbl, mul_sub, map_sub]

theorem toCols₁_add' (x y : Matrix α (β ⊕ β) E) : (x + y).toCols₁ = x.toCols₁ + y.toCols₁ := rfl
theorem toCols₂_add' (x y : Matrix α (β ⊕ β) E) : (x + y).toCols₂ = x.toCols₂ + y.toCols₂ := rfl
theorem toCols₁_smul' (r : R) (x : Matrix α (β ⊕ β) E) : (r • x).toCols₁ = r • x.toCols₁ := rfl
theorem toCols₂_smul' (r : R) (x : Matrix α (β ⊕ β) E) : (r • x).toCols₂ = r • x.toCols₂ := rfl

variable [Invertible (2 : R)]

def dblD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA (GlobalTheory.WeilM.dbl JB)) (κ ⊕ κ) where
  e :=
    { toFun := fun x => (Sum.elim (d.e x.toCols₁).1 (d.e x.toCols₂).1, Sum.elim (d.e x.toCols₁).2 (-(d.e x.toCols₂).2))
      invFun := fun q => Matrix.fromCols (d.e.symm (q.1 ∘ Sum.inl, q.2 ∘ Sum.inl))
        (d.e.symm (q.1 ∘ Sum.inr, -(q.2 ∘ Sum.inr)))
      map_add' := fun x y => by
        ext (i | i) <;> simp [toCols₁_add', toCols₂_add'] <;> abel
      map_smul' := fun r x => by
        ext (i | i) <;> simp [toCols₁_smul', toCols₂_smul']
      left_inv := fun x => by
        conv_rhs => rw [← Matrix.fromCols_toCols x]
        beta_reduce
        congr 1
        · exact d.e.symm_apply_apply x.toCols₁
        · have h : (((Sum.elim (d.e x.toCols₁).1 (d.e x.toCols₂).1) ∘ Sum.inr,
              -((Sum.elim (d.e x.toCols₁).2 (-(d.e x.toCols₂).2)) ∘ Sum.inr)) : (κ → R) × (κ → R)) =
              d.e x.toCols₂ := Prod.ext rfl (funext fun i => neg_neg _)
          exact (congrArg d.e.symm h).trans (d.e.symm_apply_apply _)
      right_inv := fun q => by
        ext (i | i) <;> simp }
  form w w' := by
    rw [symp_dbl, d.form, d.form]
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    ring

theorem isDblCoord_dblD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) : GlobalTheory.WeilM.IsDblCoord c ξ JA JB d (dblD c d) := by
  intro w₁ w₂
  simp [dblD]

end Gen

section Reindex

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem symp_submatrix (e : γ ≃ β) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α γ E) :
    GlobalTheory.WeilM.symp c ξ JA (JB.submatrix e e) x y =
      GlobalTheory.WeilM.symp c ξ JA JB (x.submatrix id e.symm) (y.submatrix id e.symm) := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← e.symm.sum_comp]
  simp

variable [Invertible (2 : R)]

def reD (e : γ ≃ β) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {J' : Matrix γ γ E} (h : J' = JB.submatrix e e)
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA J') κ where
  e := (Matrix.reindexLinearEquiv R E (Equiv.refl α) e).trans d.e
  form w w' := by
    rw [h, symp_submatrix, d.form]
    rfl

theorem reD_e (e : γ ≃ β) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {J' : Matrix γ γ E} (h : J' = JB.submatrix e e)
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (x : Matrix α γ E) :
    (reD c e h d).e x = d.e (x.submatrix id e.symm) := rfl

end Reindex

section Group

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

def reG (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e) :
    GlobalTheory.WeilM.UG c J →* GlobalTheory.WeilM.UG c J' :=
  ((Units.map (Matrix.reindexAlgEquiv E E e.symm).toAlgHom.toMonoidHom).comp (GlobalTheory.WeilM.UG c J).subtype).codRestrict
    (GlobalTheory.WeilM.UG c J') fun g => by
      have hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
      show (((g : GL β E) : Matrix β β E).submatrix e e)ᵀ * J' * (((g : GL β E) : Matrix β β E).submatrix e e).map c = J'
      rw [h, Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]

theorem reG_val (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e) (g : GlobalTheory.WeilM.UG c J) :
    ((reG c e h g : GL γ E) : Matrix γ γ E) = ((g : GL β E) : Matrix β β E).submatrix e e := rfl

end Group

section Host

variable {D : D7}

def JBd (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) :
    Matrix (Fin (GlobalTheory.Doubling.dblSp S).rank) (Fin (GlobalTheory.Doubling.dblSp S).rank) D.host.E :=
  (GlobalTheory.WeilM.dbl JB).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem incM_JBd (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) :
    incM D.host.F (JBd S JB) =
      (GlobalTheory.WeilM.dbl (incM D.host.F JB)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp [JBd, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.WeilM.dbl, h1, h2]

variable [Invertible (2 : AF D.host.F)]

def ddr {S T : HSp D} {ξ : AF D.host.F ⊗[D.host.F] D.host.E} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F (JBd S JB)))
      (κ ⊕ κ) :=
  reD _ finSumFinEquiv.symm (incM_JBd S JB) (dblD _ co)

end Host

section HostGroup

variable {D : D7}

def omdOf {S T : HSp D} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {X : Type} [AddCommGroup X] [Module ℂ X]
    (omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (JBd S JB)) →* Module.End ℂ X) :
    GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)) →* Module.End ℂ X :=
  omd₀.comp ((MonoidHom.inr _ _).comp (reG _ finSumFinEquiv.symm (incM_JBd S JB)))

end HostGroup

end GlobalTheory.DblSchr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainSaturatedFundamentalSetFrames
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

namespace GlobalTheory.FundFrames

open scoped Pointwise

theorem isFundamentalDomain_satFrames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {c : ℝ≥0∞}, HaarChart X c → ∀ {x0 : Frame X.Ψ r}, IsOrth X x0 → ∀ {FF : Set (V (nd X))}, IsFundSet X x0 FF → ∀ (Λ : Subgroup (RealGrp X)), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) → IsFundamentalDomain Λ (frameOf X ⁻¹' GlobalTheory.Unfold.satFrames X x0 FF) (haarR X) := by
  intro E _ _ _ r X c hH x0 ho FF hF Λ hΛ
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  set S := GlobalTheory.Unfold.satFrames X x0 FF with hSdef
  have hS : MeasurableSet S := GlobalTheory.Unfold.measurableSet_satFrames X ho hF.1 hF.2.1

  have hmemT : ∀ (s : Λ) (g : RealGrp X) (γ : GL (Fin r) E), lact γ (baseFr X) = frameOf X s →
      (g ∈ s • (frameOf X ⁻¹' S) ↔ lact γ⁻¹ (frameOf X g) ∈ S) := by
    intro s g γ e
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_preimage]
    have h1 : lact γ (frameOf X (s⁻¹ • g)) = frameOf X g := by
      rw [GlobalTheory.PeterssonCompare.lact_frameOf X e, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv,
        mul_inv_cancel_left]
    have h2 : frameOf X (s⁻¹ • g) = lact γ⁻¹ (frameOf X g) := by
      rw [← h1, FundSetPf.lact_inv]
    rw [h2]
  refine ⟨(GlobalTheory.PeterssonCompare.measurable_frameOf X hS).nullMeasurableSet, ?_, ?_⟩
  ·
    set G' : Set (Frame X.Ψ r) := ⋃ γ : X.Γ, (fun y => lact (γ.1)⁻¹ y) ⁻¹' S with hG'def
    have hG' : MeasurableSet G' :=
      MeasurableSet.iUnion fun γ => (GlobalTheory.Unfold.continuous_lact X _).measurable hS
    have hmemG : ∀ y, y ∈ G' ↔ ∃ γ ∈ X.Γ, lact γ⁻¹ y ∈ S := by
      intro y
      simp only [G', Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨γ, hy⟩; exact ⟨γ.1, γ.2, hy⟩
      · rintro ⟨γ, hγ, hy⟩; exact ⟨⟨γ, hγ⟩, hy⟩
    have hGB : ∀ y, ∀ b ∈ Bor X.Ψ r, rmul y b ∈ G' ↔ y ∈ G' := by
      intro y b hb
      simp only [hmemG, FundSetPf.lact_rmul, hSdef, GlobalTheory.Unfold.rmul_mem_satFrames_iff X x0 FF _ hb]
    set φ : Frame X.Ψ r → ℝ≥0∞ := G'ᶜ.indicator 1 with hφdef
    have hφm : Measurable φ := measurable_const.indicator hG'.compl
    have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x := by
      intro x _ b hb
      have hiff : rmul x b ∈ G'ᶜ ↔ x ∈ G'ᶜ := by
        simp only [Set.mem_compl_iff, hGB x b hb]
      by_cases hx : x ∈ G'ᶜ
      · rw [hφdef, Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]; rfl
      · rw [hφdef, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hiff.1 h'))]
    have hbo : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
    have h1 : GlobalTheory.SubgroupUnfold.IsIsom X.Gm (1 : GL (Fin r) E) := by
      intro v w; simp
    have hae := GlobalTheory.SubgroupUnfold.ae_mem_orbit_satFrames X ho hF hbo h1
    have hz : ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) = 0 := by
      rw [← lintegral_zero (μ := muF X (baseFr X))]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with z hz
      obtain ⟨γ, hγ, hm⟩ := hz
      rw [mul_one] at hm
      have : cpt X (baseFr X) z ∉ G'ᶜ := by
        rw [Set.mem_compl_iff, not_not, hmemG]; exact ⟨γ, hγ, hm⟩
      show φ _ = 0
      rw [hφdef, Set.indicator_of_notMem this]
    have hint := hH φ hφm hφB
    rw [hz, mul_zero] at hint
    have hae2 := (lintegral_eq_zero_iff (hφm.comp (GlobalTheory.PeterssonCompare.measurable_frameOf X))).1 hint
    filter_upwards [hae2] with g hg
    have hg' : φ (frameOf X g) = 0 := hg
    have hn : frameOf X g ∉ G'ᶜ := fun hm => by
      rw [hφdef, Set.indicator_of_mem hm] at hg'; exact one_ne_zero hg'
    rw [Set.mem_compl_iff, not_not, hmemG] at hn
    obtain ⟨γ, hγ, hm⟩ := hn
    obtain ⟨s, hs⟩ := GlobalTheory.PeterssonCompare.exists_translation X (X.Γ.inv_mem hγ)
    refine ⟨⟨s, (hΛ s).2 ⟨γ⁻¹, X.Γ.inv_mem hγ, hs⟩⟩, ?_⟩
    show frameOf X (s * g) ∈ S
    rw [← GlobalTheory.PeterssonCompare.lact_frameOf X hs]
    exact hm
  ·
    intro s t hst
    refine Disjoint.aedisjoint (Set.disjoint_left.2 fun g hgs hgt => hst ?_)
    obtain ⟨γ, hγ, e⟩ := (hΛ s).1 s.2
    obtain ⟨γ', hγ', e'⟩ := (hΛ t).1 t.2
    have h1 := (hmemT s g γ e).1 hgs
    have h2 := (hmemT t g γ' e').1 hgt
    obtain rfl := GlobalTheory.Unfold.unique_translate X hF hγ hγ' h1 h2
    exact Subtype.ext (GlobalTheory.PeterssonCompare.frameOf_injective X (e.symm.trans e'))

end GlobalTheory.FundFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralBaseChangeRationalFunctionFieldFiniteV
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.PureTransc

theorem isDomain_tensor (k : Type) [Field k] (σ : Type) (A : Type) [CommRing A] [IsDomain A]
    [Algebra k A] : IsDomain (FractionRing (MvPolynomial σ k) ⊗[k] A) := by
  let P := MvPolynomial σ k
  let K := FractionRing P
  letI : Algebra (P ⊗[k] A) (K ⊗[k] A) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P K) (AlgHom.id k A)).toAlgebra
  haveI : IsScalarTower P (P ⊗[k] A) (K ⊗[k] A) :=
    .of_algebraMap_eq fun x => by simp [RingHom.algebraMap_toAlgebra]
  haveI := IsLocalization.tensorProduct_tensorProduct k A (nonZeroDivisors P) K
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  let e : P ⊗[k] A ≃+* MvPolynomial σ A :=
    ((Algebra.TensorProduct.comm k P A).toRingEquiv.trans
      (MvPolynomial.scalarRTensorAlgEquiv).toRingEquiv)
  haveI : IsDomain (P ⊗[k] A) := e.toMulEquiv.isDomain
  have hinj : Function.Injective (algebraMap P (P ⊗[k] A)) :=
    Algebra.TensorProduct.includeLeft_injective (S := P) (algebraMap k A).injective
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (K ⊗[k] A)
    (M := Algebra.algebraMapSubmonoid (P ⊗[k] A) (nonZeroDivisors P)) ?_
  rintro _ ⟨p, hp, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero fun h =>
    nonZeroDivisors.ne_zero hp (hinj (h.trans (map_zero _).symm))

theorem isIntegral_of_isPullback : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X),
    IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) →
    IsIntegral X' := by
  intro k _ N X X' _ f f' π H

  have chart (x : X) : ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (_ : IsDomain A)
      (j : Sp A ⟶ X) (_ : IsOpenImmersion j) (q : PrimeSpectrum A),
      j q = x ∧ j ≫ f = spMap (algebraMap k A) := by
    obtain ⟨A, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f x
    have : Nonempty (Spec (.of A)) := ⟨q⟩
    have : IsIntegral (Spec (.of A)) := isIntegral_of_isOpenImmersion j
    have : IsDomain A := (affine_isIntegral_iff (.of A)).1 this
    exact ⟨A, _, _, this, j, inferInstance, q, hq, hj⟩
  have lift {A : Type} [CommRing A] [Algebra k A] [IsDomain A] (j : Sp A ⟶ X) [IsOpenImmersion j]
      (hj : j ≫ f = spMap (algebraMap k A)) (x' : X') (hx : π x' ∈ Set.range j) :
      ∃ (j₀ : Sp (FractionRing (MvPolynomial (Fin N) k) ⊗[k] A) ⟶ X') (_ : IsOpenImmersion j₀),
        x' ∈ Set.range j₀ := by
    obtain ⟨j₀, hj₀, H'⟩ := exists_affine_chart_of_isPullback H j hj
    refine ⟨j₀, hj₀, ?_⟩
    have hr : x' ∈ Set.range (Limits.pullback.fst π j) := by
      rw [Scheme.Pullback.range_fst]; exact hx
    obtain ⟨z, rfl⟩ := hr
    exact ⟨H'.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, H'.isoPullback_inv_fst]⟩
  have hflat : Flat π := by
    refine MorphismProperty.of_isPullback H.flip ?_
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    exact GlobalTheory.GeomIrr.flat_of_field _
  have : IsReduced X' := by
    have (x' : X') : _root_.IsReduced (X'.presheaf.stalk x') := by
      obtain ⟨A, _, _, _, j, _, q, hq, hj⟩ := chart (π x')
      obtain ⟨j₀, _, z, rfl⟩ := lift j hj x' ⟨q, hq⟩
      have := isDomain_tensor k (Fin N) A
      exact isReduced_of_injective
        (asIso (j₀.stalkMap z)).commRingCatIsoToRingEquiv.toRingHom
        (asIso (j₀.stalkMap z)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk X'
  have : IrreducibleSpace X' := by
    obtain ⟨A, _, _, _, j, _, q, hq, hj⟩ := chart (genericPoint X)
    obtain ⟨j₀, hj₀, H'⟩ := exists_affine_chart_of_isPullback H j hj
    have := isDomain_tensor k (Fin N) A
    have hirr : IsIrreducible (Set.range j₀) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ j₀.continuous.continuousOn
    have hdense : closure (Set.range j₀) = Set.univ := by
      refine Set.eq_univ_of_forall fun x' => ?_
      obtain ⟨y, hy, e⟩ := Flat.generalizingMap π (genericPoint_specializes (π x'))
      have hr : y ∈ Set.range (Limits.pullback.fst π j) := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, e]; exact ⟨q, hq⟩
      obtain ⟨z, hz⟩ := hr
      have hy' : y ∈ Set.range j₀ :=
        ⟨H'.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, H'.isoPullback_inv_fst, hz]⟩
      exact closure_mono (Set.singleton_subset_iff.2 hy') (specializes_iff_mem_closure.1 hy)
    refine (irreducibleSpace_def X').2 ?_
    rw [Set.top_eq_univ, ← hdense]
    exact hirr.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced X'

end GlobalTheory.PureTransc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
section
noncomputable section

namespace GlobalTheory.IndLine

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def KEqOn (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (V : Submodule ℂ P) (T : P →ₗ[ℂ] P) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → p f ∈ V →
    ∀ g ∈ M.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) g g₁ → T (p f) = p g →
      T (p f₁) = p g₁

end GlobalTheory.IndLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d}

def PGen (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (V : Submodule ℂ P) : Prop :=
  ∀ N : Submodule ℂ P, V ≤ N →
    (∀ γ ∈ Lines σ W, (∀ s, γ s ∈ unip σ W H') → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    (∀ γ ∈ Lines σ W, (∃ (t : Multiplicative ℝ →* (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (γ₁ : Multiplicative ℝ →* UA σ W₁.J), γ₁ ∈ Lines σ W₁ ∧
        ∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    N = ⊤

def KStab (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (V : Submodule ℂ P) : Prop :=
  (∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f ∈ V → p f₁ ∈ V) ∧
    ∀ γ ∈ Lines σ W, (∀ s, γ s ∈ KInf σ W B.emb) → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ V → p f₁ ∈ V

end GlobalTheory.IndLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerFormApply
section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

namespace GlobalTheory.HTRho

theorem finrank_homO_eq_quot_mSub : ∀ {k O C W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : C →+* k),
    (∀ c, τ (algebraMap C O c) = χ c • 1) →
    finrank k (homO σW τ) = finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := by
  intro k O C W V _ _ _ _ _ _ _ _ _ _ σW τ χ hτ
  have hker : ∀ T : W →ₗ[k] V, T ∈ homO σW τ → mSub σW χ ⊤ ≤ LinearMap.ker T := by
    intro T hT
    rw [mem_homO] at hT
    refine Submodule.span_le.mpr ?_
    rintro z ⟨c, x, -, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hT, hτ, LinearMap.smul_apply,
      Module.End.one_apply, sub_self]
  let qa := qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))
  let e : homO qa τ ≃ₗ[k] homO σW τ :=
    { toFun := fun f => ⟨f.1 ∘ₗ (mSub σW χ ⊤).mkQ, by
        rw [mem_homO]
        intro a x
        have h := (mem_homO _ _ _).mp f.2 a ((mSub σW χ ⊤).mkQ x)
        change f.1 ((mSub σW χ ⊤).mkQ (σW a x)) = τ a (f.1 ((mSub σW χ ⊤).mkQ x))
        rw [← qAct_mk]
        exact h⟩
      invFun := fun T => ⟨(mSub σW χ ⊤).liftQ T.1 (hker T.1 T.2), by
        rw [mem_homO]
        intro a y
        induction y using Submodule.Quotient.induction_on with
        | H x =>
          have h := (mem_homO _ _ _).mp T.2 a x
          change (mSub σW χ ⊤).liftQ T.1 _ (qa a ((mSub σW χ ⊤).mkQ x)) = τ a ((mSub σW χ ⊤).liftQ T.1 _ ((mSub σW χ ⊤).mkQ x))
          simp only [qa, qAct_mk, Submodule.liftQ_mkQ, Submodule.mkQ_apply, Submodule.liftQ_apply]
          exact h⟩
      map_add' := fun f g => by ext; rfl
      map_smul' := fun c f => by ext; rfl
      left_inv := fun f => by
        ext y
        rfl
      right_inv := fun T => by ext; rfl }
  exact e.finrank_eq.symm

end GlobalTheory.HTRho
end

