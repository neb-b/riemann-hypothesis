module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0262
public import Formalism.ThetaSupremumBounds.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMapClosedFibre
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

namespace GlobalTheory


set_option backward.isDefEq.respectTransparency.types false in
theorem fibre_finite_isClosed_of_affine_finite {X Y : Scheme.{0}} (f : Y ⟶ X) (V : X.Opens)
    (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hfin : letI := (f.app V).hom.toAlgebra; Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V))
    (x : X) (hxV : x ∈ V) (hx : IsClosed ({x} : Set X)) :
    (f.base ⁻¹' {x}).Finite ∧ ∀ y : Y, f.base y = x → IsClosed ({y} : Set Y) := by
  haveI : IsAffine V.toScheme := hV
  haveI : IsAffine (f ⁻¹ᵁ V).toScheme := hU
  haveI hg : IsFinite (f ∣_ V) := by
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    refine ⟨inferInstance, ?_⟩
    have h1 : (f.app (V.ι ''ᵁ ⊤)).hom.Finite := by
      rw [Scheme.Opens.ι_image_top]; exact hfin
    have h2 : ∀ {A B : CommRingCat.{0}} (e : A ⟶ B) [IsIso e], e.hom.Finite := fun e _ =>
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso e).2
    rw [morphismRestrict_appTop]
    exact (h2 _).comp h1
  have hmemU : ∀ y : Y, f.base y = x → y ∈ f ⁻¹ᵁ V := fun y hy => by
    show f.base y ∈ V
    rw [hy]; exact hxV
  have hres : ∀ (y : Y) (hy : f.base y = x),
      (f ∣_ V) (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) = (⟨x, hxV⟩ : V.toScheme) := by
    intro y hy
    exact Subtype.ext ((morphismRestrict_base_coe f V _).trans hy)
  refine ⟨?_, ?_⟩
  · refine (((f ∣_ V).finite_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).image
      (f ⁻¹ᵁ V).ι.base).subset ?_
    intro y hy
    exact ⟨⟨y, hmemU y hy⟩, hres y hy, rfl⟩
  · intro y hy
    rw [← closure_subset_iff_isClosed]
    intro z hz
    rw [← specializes_iff_mem_closure] at hz
    have hfz : f.base z = x := by
      have h1 : f.base y ⤳ f.base z := hz.map f.base.hom.continuous
      rw [hy, specializes_iff_mem_closure, hx.closure_eq] at h1
      exact h1
    have hspec : (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) ⤳ ⟨z, hmemU z hfz⟩ :=
      (f ⁻¹ᵁ V).ι.isOpenEmbedding.isInducing.specializes_iff.1 hz
    have hdisc := ((f ∣_ V).isDiscrete_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).to_subtype
    have hs2 : (⟨_, hres y hy⟩ : ((f ∣_ V) ⁻¹' {(⟨x, hxV⟩ : V.toScheme)} : Set _)) ⤳
        ⟨_, hres z hfz⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.1 hspec
    have := congrArg (fun p => (p.1 : (f ⁻¹ᵁ V).toScheme).1) hs2.eq
    exact (Set.mem_singleton_iff.2 this.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSubstLe
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions Formalism.L2.DIV
open Formalism.REAL (fockF)
open GlobalTheory.SubstMem (padRows)
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.JetBlock

abbrev incl {a b : ℕ} (h : a ≤ b) : Fin a × Fin a → Fin b × Fin b := Prod.map (Fin.castLE h) (Fin.castLE h)

theorem incl_injective {a b : ℕ} (h : a ≤ b) : Function.Injective (incl h) :=
  (Fin.castLE_injective h).prodMap (Fin.castLE_injective h)

theorem fockF_rename {σ τ : Type} {e : σ → τ} (he : Function.Injective e) (f g : MvPolynomial σ ℂ) :
    fockF (rename e f) (rename e g) = fockF f g := by
  rw [GlobalTheory.LvT.PtNorm.fockF_eq, GlobalTheory.LvT.PtNorm.fockF_eq, fockL_apply, fockL_apply, GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename he]

theorem fockF_rowAct {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF (rowAct ℂ g f) (rowAct ℂ g f) = fockF f (rowAct ℂ (g * gᴴ) f) := by
  rw [fockRowAdj, ← rowActMul ℂ r n]
  rfl

theorem sum_castLE {M : Type} [AddCommMonoid M] {a b : ℕ} (h : a ≤ b) (F : Fin b → M)
    (hF : ∀ t : Fin b, a ≤ t.val → F t = 0) : ∑ t, F t = ∑ q : Fin a, F (Fin.castLE h q) := by
  symm
  refine Finset.sum_of_injOn (Fin.castLE h) (fun _ _ _ _ e => Fin.castLE_injective h e)
    (fun _ _ => Finset.mem_univ _) ?_ (fun _ _ => rfl)
  intro t _ ht
  refine hF t ?_
  by_contra h'
  exact ht ⟨⟨t.val, by omega⟩, by simp, by ext; simp⟩

theorem rowAct_pad {a b : ℕ} (h : a ≤ b) (A : Matrix (Fin a) (Fin b) ℂ) (f : MvPolynomial (Fin a × Fin a) ℂ) :
    rowAct ℂ (padRows A * (padRows A)ᴴ) (rename (incl h) f) = rename (incl h) (rowAct ℂ (A * Aᴴ) f) := by
  have e : (rowAct ℂ (padRows A * (padRows A)ᴴ)).comp (rename (incl h)) =
      (rename (incl h)).comp (rowAct ℂ (A * Aᴴ)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨p, q⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, rename_X, rowAct, aeval_X, map_sum, map_mul, rename_C, Prod.map]
    rw [sum_castLE h]
    · refine Finset.sum_congr rfl fun β _ => ?_
      simp [Matrix.mul_apply, padRows]
    · intro t ht
      simp [Matrix.mul_apply, padRows, not_lt.mpr ht]
  exact DFunLike.congr_fun e f

theorem exists_sing {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) :
    ∃ (U : Matrix (Fin a) (Fin a) ℂ) (t : Fin a → ℝ), U * Uᴴ = 1 ∧ Antitone t ∧ (∀ i, 0 ≤ t i) ∧
      A * Aᴴ = (U * Matrix.diagonal fun i => (t i : ℂ)) * (U * Matrix.diagonal fun i => (t i : ℂ))ᴴ ∧
      ∑ i, t i ^ 2 = ∑ β, ∑ α, ‖A α β‖ ^ 2 := by
  have hP : (A * Aᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  have hH := hP.isHermitian
  set ev := hH.eigenvalues with hev
  have h0 : ∀ i, 0 ≤ ev i := hP.eigenvalues_nonneg
  set σ := Tuple.sort (fun i => -ev i) with hσ
  have hm : Monotone ((fun i => -ev i) ∘ σ) := Tuple.monotone_sort _
  set V : Matrix (Fin a) (Fin a) ℂ := hH.eigenvectorUnitary.1 with hV
  have hVV : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hs : A * Aᴴ = V * Matrix.diagonal (fun i => (ev i : ℂ)) * Vᴴ := by
    have := hH.spectral_theorem
    exact this
  refine ⟨V.submatrix id σ, fun i => √(ev (σ i)), ?_, ?_, fun i => Real.sqrt_nonneg _, ?_, ?_⟩
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hVV]
    simp
  · intro i j hij
    have := hm hij
    simp only [Function.comp] at this
    exact Real.sqrt_le_sqrt (by linarith)
  · rw [hs]
    ext i j
    simp only [Matrix.mul_apply (M := _ * _), Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ((ev (σ k) : ℝ) : ℂ) = (√(ev (σ k)) : ℝ) * (√(ev (σ k)) : ℝ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (h0 _)]
    rw [star_mul']
    simp only [Complex.star_def, Complex.conj_ofReal]
    conv_lhs => rw [this]
    ring
  · simp only [Real.sq_sqrt (h0 _)]
    rw [Equiv.sum_comp σ ev]
    have h1 := hH.trace_eq_sum_eigenvalues
    apply Complex.ofReal_injective
    push_cast
    rw [hev]
    erw [← h1]
    rw [Finset.sum_comm]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.mul_conj']

theorem dominance {n : ℕ} (ν : Fin n → ℕ) {f : MvPolynomial (Fin n × Fin n) ℂ} (hf : f ∈ dualWeyl ℂ n n ν) :
    ∀ m ∈ f.support, (∀ k : ℕ, (∑ a : Fin n with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t) ∧
      ∑ a : Fin n, rowDeg m a = ∑ t : Fin n, ν t := by
  classical
  rw [standardMonomialSpanDomain ℂ n n ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, rfl, rfl⟩ := hx
    exact fun m hm => bidetDominance ℂ n n K sz hsz I m hm
  | zero => simp
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx => exact fun m hm => hx m (support_smul hm)

theorem fock_subst_le {a b : ℕ} (h : a ≤ b) (A : Matrix (Fin a) (Fin b) ℂ) :
    ∃ t : Fin a → ℝ, (∀ i, 0 ≤ t i) ∧ ∑ i, t i ^ 2 = ∑ β, ∑ α, ‖A α β‖ ^ 2 ∧
      ∀ (ν : Fin a → ℕ), ∀ f ∈ dualWeyl ℂ a a ν,
        (fockF (rowAct ℂ (padRows A) (rename (incl h) f)) (rowAct ℂ (padRows A) (rename (incl h) f))).re ≤
          (∏ i, t i ^ (2 * ν i)) * (fockF f f).re := by
  obtain ⟨U, t, hU, ht, h0, hA, hs⟩ := exists_sing A
  refine ⟨t, h0, hs, fun ν f hf => ?_⟩
  have hd := dominance ν (dualWeylRowStable ℂ a a ν U f hf)
  have h1 := fockDiagBound a a t ν h0 ht (rowAct ℂ U f) (fun m hm => (hd m hm).1) (fun m hm => (hd m hm).2)
  rw [fockF_rowAct U, hU, ldlat_rowAct_one, ← AlgHom.comp_apply, rowActMul, fockF_rowAct, ← hA] at h1
  rw [fockF_rowAct, rowAct_pad, fockF_rename (incl_injective h)]
  exact h1

theorem rename_hw {a b : ℕ} (h : a ≤ b) (ν : Fin a → ℕ) :
    rename (incl h) (hw ℂ (le_refl a) ν) = hw ℂ (le_refl b) (rowNu (r := b) ν) := by
  rw [← GlobalTheory.Proof.ColumnInclusionRenaming.rename_hw h]
  unfold hw
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, map_pow]
  congr 1
  unfold lpMinor
  rw [AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext p q : 2
  simp [GlobalTheory.Proof.ColumnInclusionRenaming.colIncl]


open GlobalTheory.DualWeyl GlobalTheory.WeylMinorDual in
theorem fock_mul_det {n : ℕ} (μ : Fin n → ℕ) (hμ : Antitone μ) (e : ℕ) {f : MvPolynomial (Fin n × Fin n) ℂ}
    (hf : f ∈ dualWeyl ℂ n n μ) :
    fockF (f * gdet ℂ n ^ e) (f * gdet ℂ n ^ e) /
        fockF (hw ℂ (le_refl n) fun i => μ i + e) (hw ℂ (le_refl n) fun i => μ i + e) =
      fockF f f / fockF (hw ℂ (le_refl n) μ) (hw ℂ (le_refl n) μ) := by
  have hν : Antitone fun i => μ i + e := fun i j hij => Nat.add_le_add_right (hμ hij) e
  have hm : f * gdet ℂ n ^ e ∈ dualWeyl ℂ n n fun i => μ i + e :=
    (dualWeylMul ℂ n n _ _ _ _).1 hf (GlobalTheory.SubstMem.det_pow_mem n e)
  have hn : ∀ (g : UN n) (p : Pol n ℂ), ‖evalAt g.1 (p * gdet ℂ n ^ e)‖ = ‖evalAt g.1 p‖ := by
    intro g p
    have h1 : evalAt g.1 (gdet ℂ n) = g.1.det := by
      unfold gdet
      rw [AlgHom.map_det]
      congr 1
      ext i j
      simp
    rw [map_mul, map_pow, h1, norm_mul, norm_pow,
      CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary g.2), one_pow, mul_one]
  have h1 := (_root_.GlobalTheory.DualWeyl.Repro.extremal_reproducing n μ hμ).2
  have h2 := (_root_.GlobalTheory.DualWeyl.Repro.extremal_reproducing n _ hν).2
  rw [GlobalTheory.DualWeyl.extremal, hw_add] at h2
  simp only [GlobalTheory.DualWeyl.normSq, hn] at h2
  rw [GlobalTheory.DualWeyl.normSq, GlobalTheory.DualWeyl.extremal] at h1
  have hd : (dim (fun i => μ i + e) : ℝ) = dim μ := by
    refine mul_right_cancel₀ (fun h0 => ?_) (h2.trans h1.symm)
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  have e1 := GlobalTheory.DualWeylFock.form_eq_fock_div n μ hμ f hf f hf
  have e2 := GlobalTheory.DualWeylFock.form_eq_fock_div n _ hν _ hm _ hm
  rw [form_self] at e1 e2
  refine e2.symm.trans (Eq.trans ?_ e1)
  simp only [GlobalTheory.DualWeyl.normSq, hn, hd]

end GlobalTheory.JetBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesCohomologous
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameCob

theorem res_comp {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) (x : Γ(X, U)) = _
  rw [← Functor.map_comp]
  rfl

theorem comm_group_step {G : Type*} [CommGroup G] (a b c d e f g k : G) (A : a * b = c * d) (B : b = e * f)
    (C : d = g * k) : e * a * g⁻¹ * f = c * k := by
  subst B C
  calc e * a * g⁻¹ * f = g⁻¹ * (a * (e * f)) := by ac_rfl
    _ = g⁻¹ * (c * (g * k)) := by rw [A]
    _ = c * k := by rw [mul_left_comm c, inv_mul_cancel_left]

theorem frames_cohomologous : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X)
    (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), L.IsLB → L'.IsLB → LBIso L L' →
    IsFrame L V hV u → IsFrame L' V hV u' →
    ∃ t : ∀ T : C, Γ(X, V T)ˣ, ∀ T T' a, u' T T' a * res (hV a) (t T) = t T' * u T T' a := by
  intro X C _ V hV L L' u u' hL hL' ⟨w, hw⟩ ⟨τ, hτg, hτ⟩ ⟨τ', hτ'g, hτ'⟩
  choose t ht htu using fun T => _root_.GlobalTheory.GenRatio.exists_unique_ratio X L L' (V T) w (τ T) (τ' T) hL hL' hw (hτg T) (hτ'g T)
  refine ⟨t, fun T T' a => ?_⟩
  have key : u' T T' a * res (hV a) (t T) * (u T T' a)⁻¹ = t T' := by
    refine htu T' _ (fun m m' => ?_)
    have hO : V T' ⊓ (L'.U m' ⊓ L.U m) ≤ V T ⊓ (L'.U m' ⊓ L.U m) := inf_le_inf_right _ (hV a)
    have A := congrArg (res hO) (ht T m m')
    have B := congrArg (res (inf_le_inf_left (V T') inf_le_left :
      V T' ⊓ (L'.U m' ⊓ L.U m) ≤ V T' ⊓ L'.U m')) (hτ' T T' a m')
    have C' := congrArg (res (inf_le_inf_left (V T') inf_le_right :
      V T' ⊓ (L'.U m' ⊓ L.U m) ≤ V T' ⊓ L.U m)) (hτ T T' a m)
    simp only [map_mul, map_inv, res_comp] at A B C' ⊢
    erw [res_comp] at A
    exact comm_group_step _ _ _ _ _ _ _ _ A B C'
  rw [← key, inv_mul_cancel_right]

end GlobalTheory.FrameCob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalIdealFrobeniusPowers
section
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace GlobalTheory.SmGL.CuspSpan

theorem blk_two_apply {α β n : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (c : α ⊕ β ≃ n) (s : α ⊕ β) : GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two c) (c s) = s.isRight := by
  rcases s with p | q
  · rw [← GlobalTheory.SmGL.two_false, GlobalTheory.SmGL.blk_apply]; rfl
  · rw [← GlobalTheory.SmGL.two_true, GlobalTheory.SmGL.blk_apply]; rfl

theorem mem_span_unip (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : GlobalTheory.SmGL.IsCuspidal π) (a b : ℕ)
    (e : Fin N ≃ Fin a ⊕ Fin b) (ha : 0 < a) (hb : 0 < b)
    (u : (Fin a → Fin b → k) → GL (Fin N) k)
    (hu : ∀ X, (u X : Matrix (Fin N) (Fin N) k) =
      Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) (w : V) :
    w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} := by
  have h : a + b = N := by
    have := Fintype.card_congr e
    simpa using this.symm
  have H := ((GlobalTheory.SmGL.CuspMax.isCuspidal_iff_maximal k N V π).1 hπ).2 a b h ha hb
  have H' : Subsingleton (Jacquet π (unipRad k (GlobalTheory.SmGL.two e.symm))) := by
    refine GlobalTheory.SmGL.CuspMax.subsingleton_jacquet_of_perm π (e.trans (stdSum h)) (fun i j hij => ?_) H
    have h1 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (stdSum h)) ((e.trans (stdSum h)) i) = (e i).isRight :=
      fun i => blk_two_apply (stdSum h) (e i)
    have h2 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two e.symm) i = (e i).isRight := fun i => by
      have := blk_two_apply e.symm (e i)
      rwa [Equiv.symm_apply_apply] at this
    rw [h1, h1] at hij
    rw [h2, h2]
    exact hij
  have htop : twKer π (unipRad k (GlobalTheory.SmGL.two e.symm)) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 H'
  have hw : w ∈ twKer π (unipRad k (GlobalTheory.SmGL.two e.symm)) 1 := htop ▸ Submodule.mem_top
  refine (Submodule.span_le.2 ?_) hw
  rintro _ ⟨n, v, rfl⟩
  refine Submodule.subset_span ⟨fun p q => (n : GL (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q)),
    v, ?_⟩
  have hn : (n : GL (Fin N) k) = u (fun p q => (n : GL (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q))) := by
    have hent := GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.1 n.2
    have h2 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two e.symm) i = (e i).isRight := fun i => by
      have := blk_two_apply e.symm (e i)
      rwa [Equiv.symm_apply_apply] at this
    ext i j
    rw [hu, Matrix.reindex_apply, Matrix.submatrix_apply]
    simp only [Equiv.symm_symm]
    obtain ⟨s, rfl⟩ := e.symm.surjective i
    obtain ⟨t, rfl⟩ := e.symm.surjective j
    simp only [Equiv.apply_symm_apply]
    rcases s with p | p <;> rcases t with q | q
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₁₁]
      simp [Matrix.one_apply]
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₂₁]
      simp [Matrix.one_apply]
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₂₂]
      simp [Matrix.one_apply]
  rw [← hn]
  simp

end GlobalTheory.SmGL.CuspSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodParameterFirstSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContragredientPar

open Finset GlobalTheory.SignedHC

theorem v_strictAnti {R : Ranks} (P : HCParam R) : StrictAnti P.v := by
  have hs : ∀ (a : ℕ) (h : a + 1 < R.k - 1), P.v ⟨a + 1, h⟩ < P.v ⟨a, by omega⟩ :=
    fun a h => (P.u_gt_v ⟨a + 1, h⟩).trans (P.v_gt_u ⟨a, by omega⟩)
  have hA : ∀ (d a : ℕ) (h : a + d + 1 < R.k - 1), P.v ⟨a + d + 1, h⟩ < P.v ⟨a, by omega⟩ := by
    intro d
    induction d with
    | zero => exact hs
    | succ d ih => intro a h; exact (hs (a + d + 1) h).trans (ih a (by omega))
  rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show a < c from hac)
  exact hA d a hc

theorem b_strictMono {R : Ranks} (P : HCParam R) : StrictMono P.b := by
  have hs : ∀ (a : ℕ) (h : a + 1 < R.m), P.b ⟨a, by omega⟩ < P.b ⟨a + 1, h⟩ := fun a h => by
    have h1 := P.gap_be ⟨a, by omega⟩
    have h2 := P.gap_eb ⟨a, by omega⟩ h
    have h3 : (0 : ℚ) ≤ R.t := by positivity
    linarith
  have hA : ∀ (d a : ℕ) (h : a + d + 1 < R.m), P.b ⟨a, by omega⟩ < P.b ⟨a + d + 1, h⟩ := by
    intro d
    induction d with
    | zero => exact hs
    | succ d ih => intro a h; exact (ih a (by omega)).trans (hs (a + d + 1) h)
  rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show a < c from hac)
  exact hA d a hc

theorem neg_v_lt_b {R : Ranks} (P : HCParam R) (i : Fin (R.k - 1)) (j : Fin R.m) : -P.v i < P.b j := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have h1 := P.u_last_gt (by omega) (by omega)
  have h2 := P.v_gt_u ⟨R.k - 2, by omega⟩
  have h3 : P.v ⟨R.k - 2, by omega⟩ ≤ P.v i :=
    (v_strictAnti P).antitone (show i.1 ≤ R.k - 2 by have := i.2; omega)
  have h4 : P.b ⟨0, by omega⟩ ≤ P.b j := (b_strictMono P).monotone (show 0 ≤ j.1 from Nat.zero_le _)
  have h5 : (⟨R.k - 2 + 1, by omega⟩ : Fin R.k) = ⟨R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
  simp only [h5] at h2
  linarith

end GlobalTheory.ContragredientPar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherDegreeClassDiesOnFinerEtaleNeighbourhoodStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.higherDegree_class_dies_on_finer_etaleNeighbourhood : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsNbhd B A' f → ∀ (m i : ℤ), 2 ≤ m → ∀ z : Ht q (sp (Localization.Away (algebraMap B A' f))) m i, ∃ (A'' : Type) (_ : CommRing A'') (_ : Algebra B A'') (_ : Algebra.Etale B A'') (φ : A' →ₐ[B] A''), IsNbhd B A'' f ∧ pull _ (spMap (awayHom φ f)) _ _ z = 0 := by
  first | (exact @GlobalTheory.KillFiner.main) | (exact GlobalTheory.KillFiner.main) | (intros; apply GlobalTheory.KillFiner.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitCongruenceSubgroupRelIndexNeZero
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt

namespace GlobalTheory.CMVal.LatEnt

theorem relIndex_congr_radN_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N →
    (congr (radN E N)).relIndex (congr (fun _ => 1)) ≠ 0 := by
  intro E _ _ N hN
  have := PicFin.finite_quot (E := E) hN.ne'
  let U : Subgroup (Af E)ˣ := congr (fun _ => 1)
  let r : U →* PicFin.intR E ⧸ Ideal.span {(N : PicFin.intR E)} :=
    { toFun := fun u => Ideal.Quotient.mk _ ⟨(u.1 : Af E), fun v =>
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (u.2 v).1.le⟩
      map_one' := map_one (Ideal.Quotient.mk _)
      map_mul' := fun a b => by rw [← map_mul]; rfl }
  have h1 : r.toHomUnits.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have h2 : ((congr (radN E N)).subgroupOf U).FiniteIndex := by
    refine Subgroup.finiteIndex_of_le (H := r.toHomUnits.ker) fun u hu w => ⟨(u.2 w).1, ?_⟩
    have h2 : Ideal.Quotient.mk (Ideal.span {(N : PicFin.intR E)}) ⟨(u.1 : Af E), fun v =>
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (u.2 v).1.le⟩ =
        Ideal.Quotient.mk _ 1 := congrArg Units.val (MonoidHom.mem_ker.1 hu)
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h2
    obtain ⟨β, hβ⟩ := h2
    have h3 : ((u.1 : (Af E)ˣ) : Af E) - 1 = (N : Af E) * β.1 := congrArg Subtype.val hβ
    rw [← map_natCast (algebraMap E (Af E))] at h3
    have h4 : ((u.1 : (Af E)ˣ) : Af E) w - 1 = algebraMap E (w.adicCompletion E) (N : E) * β.1 w :=
      congrArg (fun z : Af E => z w) h3
    show Valued.v (((u.1 : (Af E)ˣ) : Af E) w - 1) ≤ Valued.v (N : w.adicCompletion E)
    rw [h4, map_mul, map_natCast]
    exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (β.2 w))
  exact h2.1

end GlobalTheory.CMVal.LatEnt
end
end

