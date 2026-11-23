module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeComapOfExactFlat
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory

theorem isBaseChange_comap_of_exact (A E : Type) [CommRing A] [CommRing E] [Algebra A E]
    [Module.Flat A E] (D₀ D₁ D₂ : Type) [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂]
    [Module E D₀] [Module E D₁] [Module E D₂] [Module A D₀] [Module A D₁] [Module A D₂]
    [IsScalarTower A E D₀] [IsScalarTower A E D₁] [IsScalarTower A E D₂]
    (j : D₀ →ₗ[E] D₁) (q : D₁ →ₗ[E] D₂) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂)
    (hj : Function.Injective j) (hex : Function.Exact j q) (_hq : Function.Surjective q)
    (h₁ : IsBaseChange E N₁.subtype) (h₂ : IsBaseChange E N₂.subtype)
    (hN : ∀ x ∈ N₁, q x ∈ N₂) :
    IsBaseChange E (N₁.comap (j.restrictScalars A)).subtype := by
  set N₀ := N₁.comap (j.restrictScalars A) with hN₀
  let ι : N₀ →ₗ[A] N₁ := (j.restrictScalars A).restrict (fun x hx => hx)
  let f : N₁ →ₗ[A] N₂ := (q.restrictScalars A).restrict hN
  have hιv : ∀ y : N₀, (ι y : D₁) = j y := fun _ => rfl
  have hfv : ∀ y : N₁, (f y : D₂) = q y := fun _ => rfl
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply hj
    have := congrArg Subtype.val hxy
    simpa [ι] using this
  have hιf : Function.Exact ι f := by
    intro y
    constructor
    · intro hy
      have hy' : q (y : D₁) = 0 := by
        have := congrArg Subtype.val hy
        rwa [hfv] at this
      obtain ⟨x, hx⟩ := (hex (y : D₁)).1 hy'
      refine ⟨⟨x, ?_⟩, ?_⟩
      · show j x ∈ N₁
        rw [hx]; exact y.2
      · apply Subtype.ext
        simpa [ι] using hx
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      simp only [f, ι, LinearMap.restrict_apply, LinearMap.restrictScalars_apply,
        ZeroMemClass.coe_zero]
      exact (hex (j x)).2 ⟨x, rfl⟩
  have hιT : Function.Injective (LinearMap.lTensor E ι) :=
    Module.Flat.lTensor_preserves_injective_linearMap ι hι
  have hfT : Function.Exact (LinearMap.lTensor E ι) (LinearMap.lTensor E f) :=
    Module.Flat.lTensor_exact E hιf
  let Φ : E ⊗[A] N₀ →ₗ[E] D₀ := N₀.subtype.liftBaseChange E
  have hcomm₁ : ∀ t : E ⊗[A] N₀, j (Φ t) = h₁.equiv (LinearMap.lTensor E ι t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Φ, IsBaseChange.equiv_tmul, hιv]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hcomm₂ : ∀ t : E ⊗[A] N₁, h₂.equiv (LinearMap.lTensor E f t) = q (h₁.equiv t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [IsBaseChange.equiv_tmul, hfv]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hΦi : Function.Injective Φ := by
    intro s t hst
    apply hιT
    apply h₁.equiv.injective
    rw [← hcomm₁, ← hcomm₁, hst]
  have hΦs : Function.Surjective Φ := by
    intro d
    obtain ⟨t, ht⟩ := h₁.equiv.surjective (j d)
    have h0 : LinearMap.lTensor E f t = 0 := by
      apply h₂.equiv.injective
      rw [hcomm₂, ht, map_zero]
      exact (hex (j d)).2 ⟨d, rfl⟩
    obtain ⟨s, hs⟩ := (hfT t).1 h0
    refine ⟨s, hj ?_⟩
    rw [hcomm₁, hs, ht]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨hΦi, hΦs⟩) ?_
  intro x
  show Φ (1 ⊗ₜ x) = x
  simp [Φ, LinearMap.liftBaseChange_tmul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariants
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem finrank_maxUnramified_eq_cyclotomicLevel (K E : FinExt l) (s : ℕ) (hs : 1 ≤ s) (hE : E.1 = Ks K s)
    (hle : K.1 ≤ E.1) : Module.finrank ℚ_[l] ↥(K0 E) = Module.finrank ℚ_[l] ↥(K0 K) := by
  have h0 : K0 K ≤ K0 E := inf_le_inf_right _ hle
  have h1 : Ks E s = Ks K s := by
    apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rw [← hE]
      exact inf_le_left
    · exact sup_le_sup_right h0 _
  have h2 := finrank_Ks E s hs
  rw [h1, finrank_Ks K s hs] at h2
  have hlp : l.Prime := Fact.out
  have hpos : 0 < (l - 1) * l ^ (s - 1) :=
    Nat.mul_pos (Nat.sub_pos_of_lt hlp.one_lt) (pow_pos hlp.pos _)
  exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm

theorem mem_GKs_iff_mem_Gj (P : LocPrime l) (K : FinExt l) (LL : FinExt l) (n : ℕ)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (x : ↥(GK K)) :
    x ∈ W.GKs ↔ (x : GQ l) ∈ Gj K W.s := by
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have hcb := (cyc_basic l P.χQ hχ).2.2 K
  have hK0 : (x : GQ l) ∈ (K0 K).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (inf_le_left : K0 K ≤ K.1) x.2
  rw [W.GKs_def, (hcb x hK0).1 W.s, P.PD_χ, ← DictKs.le_v_iff P LL,
    (algebraMap ℚ_[l] ↥LL.1).map_sub, (algebraMap ℚ_[l] ↥LL.1).map_one]

theorem actVB_inclusion (P : LocPrime l) (K E LL : FinExt l) (hle : K.1 ≤ E.1)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (g : ↥(GK E)) :
    actVB (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) g =
      actVB (P.PD K) T.ρ (Subgroup.inclusion (GK_le hle) g) := by
  unfold actVB
  congr 1
  ext b
  change (P.PD E).actB g b = (P.PD K).actB _ b
  rw [P.PD_actB, P.PD_actB]
  rfl

theorem iInf_ker_eq {R M ι κ : Type} [Ring R] [AddCommGroup M] [Module R M]
    (f : ι → M →ₗ[R] M) (g : κ → M →ₗ[R] M) (h1 : ∀ i, ∃ k, f i = g k) (h2 : ∀ k, ∃ i, f i = g k) :
    ⨅ i, LinearMap.ker (f i) = ⨅ k, LinearMap.ker (g k) := by
  apply le_antisymm
  · refine le_iInf fun k => ?_
    obtain ⟨i, hi⟩ := h2 k
    exact hi ▸ iInf_le _ i
  · refine le_iInf fun i => ?_
    obtain ⟨k, hk⟩ := h1 i
    exact hk ▸ iInf_le _ k

theorem Dcris_eq_iInf (P : LocPrime l) (K E LL : FinExt l) (hle : K.1 ≤ E.1)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (H : Subgroup ↥(GK K))
    (hH : ∀ x : ↥(GK K), x ∈ H ↔ (x : GQ l) ∈ GK E) :
    Dcris (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) =
      ⨅ g : ↥H, LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) -
        (LinearMap.id : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.B)) := by
  unfold Dcris
  apply iInf_ker_eq
  · intro g
    refine ⟨⟨Subgroup.inclusion (GK_le hle) g, (hH _).2 g.2⟩, ?_⟩
    exact congrArg (fun f => f - LinearMap.id) (actVB_inclusion P K E LL hle T g)
  · intro g
    refine ⟨⟨(g : ↥(GK K)), (hH _).1 g.2⟩, ?_⟩
    exact congrArg (fun f => f - LinearMap.id) (actVB_inclusion P K E LL hle T _)


set_option maxHeartbeats 1600000 in
theorem isCrys_Ks_of_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (n : ℕ) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), W.s = s → ∀ (E : FinExt l), E.1 = Ks K s → ∀ (hle : K.1 ≤ E.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), Module.finrank ↥LL.1 ↥(⨅ g : ↥W.GKs, LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) - (LinearMap.id : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.B))) = Module.finrank ℚ_[l] ↥(K0 K) * Module.finrank ↥LL.1 T.V → IsCrys (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) := by
  intro l _ P K s LL n W hs E hE hle T h
  have hG : Gj K W.s = GK E := by
    rw [Gj, hs, ← hE]
    rfl
  have hD := Dcris_eq_iInf P K E LL hle T W.GKs (fun x => by
    rw [mem_GKs_iff_mem_Gj, hG])
  have h1 := finrank_maxUnramified_eq_cyclotomicLevel K E s (hs ▸ W.s_pos) hE hle
  have h2 := congrArg
    (fun D : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.B) => Module.finrank ↥LL.1 ↥D) hD
  rw [← h1] at h
  exact h2.trans h

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KapIdemMemInC
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

noncomputable section

namespace GlobalTheory.Cyc.Decomp

variable {l : ℕ} [Fact l.Prime]

theorem coe_emb_algebraMap (LL : FinExt l) (τ : ↥LL.1 →ₐ[ℚ_[l]] Om l) (x : ℤ_[l]) :
    algebraMap (Om l) (PadicComplex l) (τ ((algebraMap ℤ_[l] ↥(OL LL) x : ↥(OL LL)) : ↥LL.1)) = zC x := by
  have h : ((algebraMap ℤ_[l] ↥(OL LL) x : ↥(OL LL)) : ↥LL.1) = algebraMap ℚ_[l] ↥LL.1 (x : ℚ_[l]) := by
    rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]; rfl
  rw [h, AlgHom.commutes]; rfl

theorem exists_evEmb (LL : FinExt l) (τ : ↥LL.1 →ₐ[ℚ_[l]] Om l) :
    ∃ ev : OCO LL →+* PadicComplex l, ∀ (c : OC l) (a : ↥(OL LL)),
      ev (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) * algebraMap (Om l) (PadicComplex l) (τ (a : ↥LL.1)) := by
  letI : Algebra ℤ_[l] (PadicComplex l) :=
    ((algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom).toAlgebra
  let u : OC l →ₐ[ℤ_[l]] PadicComplex l :=
    { (PadicComplexInt l).subtype with commutes' := fun x => rfl }
  let v : ↥(OL LL) →ₐ[ℤ_[l]] PadicComplex l :=
    { (algebraMap (Om l) (PadicComplex l)).comp (τ.toRingHom.comp (OL LL).val.toRingHom) with
      commutes' := fun x => coe_emb_algebraMap LL τ x }
  exact ⟨(Algebra.TensorProduct.productMap u v).toRingHom, fun c a => rfl⟩

theorem evEmb_eq_sum {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (τ : ↥LL.1 →ₐ[ℚ_[l]] Om l) (ev : OCO LL →+* PadicComplex l)
    (hev : ∀ (c : OC l) (a : ↥(OL LL)),
      ev (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) * algebraMap (Om l) (PadicComplex l) (τ (a : ↥LL.1)))
    (x : OCO LL) :
    ev x = ∑ k, kap o x k * algebraMap (Om l) (PadicComplex l) (τ (o k : ↥LL.1)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, kap_zero, zero_mul, Finset.sum_const_zero]
  | add x y hx hy =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add ev, kap_add, hx, hy, add_mul, Finset.sum_add_distrib]
  | tmul c a =>
    rw [hev]
    simp only [kap_tmul, mul_assoc, ← Finset.mul_sum]
    congr 1
    conv_lhs => rw [← o.sum_repr a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Algebra.smul_def, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, map_sum,
      map_mul, coe_emb_algebraMap]

theorem exists_emb_det_ne_zero {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) :
    ∃ τ : Fin f → (↥LL.1 →ₐ[ℚ_[l]] Om l),
      (Matrix.of fun i j => τ j (o i : ↥LL.1) : Matrix (Fin f) (Fin f) (Om l)).det ≠ 0 := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL.1
  haveI := IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  let b := o.localizationLocalization ℚ_[l] (nonZeroDivisors ℤ_[l]) ↥LL.1
  have hb : ∀ i, b i = (o i : ↥LL.1) := fun i =>
    Module.Basis.localizationLocalization_apply _ _ _ _ i
  have hc : Fintype.card (Fin f) = Fintype.card (↥LL.1 →ₐ[ℚ_[l]] Om l) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis b]
  let e := Fintype.equivOfCardEq hc
  refine ⟨e, fun h0 => ?_⟩
  have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ_[l] (Om l) b e
  have h2 : Algebra.embeddingsMatrixReindex ℚ_[l] (Om l) b e =
      Matrix.of fun i j => e j (o i : ↥LL.1) := by
    ext i j
    simp [Algebra.embeddingsMatrixReindex, hb]
  rw [h2, h0, zero_pow two_ne_zero, map_eq_zero] at h1
  exact Algebra.discr_not_zero_of_basis ℚ_[l] b h1

theorem kap_idem_algebraic {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (e : OCO LL) (he : IsIdempotentElem e) (k : Fin f) :
    ∃ x : Om l, algebraMap (Om l) (PadicComplex l) x = kap o e k := by
  obtain ⟨τ, hτ⟩ := exists_emb_det_ne_zero o
  set M : Matrix (Fin f) (Fin f) (Om l) := Matrix.of fun i j => τ j (o i : ↥LL.1) with hM
  have hy : ∀ j, ∃ y : Om l, algebraMap (Om l) (PadicComplex l) y =
      ∑ k, kap o e k * algebraMap (Om l) (PadicComplex l) (M k j) := by
    intro j
    obtain ⟨ev, hev⟩ := exists_evEmb LL (τ j)
    have h1 := evEmb_eq_sum o (τ j) ev hev e
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 (he.map ev) with h | h
    · exact ⟨0, by rw [map_zero, ← h, h1]; rfl⟩
    · exact ⟨1, by rw [map_one, ← h, h1]; rfl⟩
  choose y hy using hy
  refine ⟨∑ j, y j * M⁻¹ j k, ?_⟩
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (Ne.isUnit hτ)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hy, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← Finset.mul_sum, ← map_mul, ← map_sum, ← Matrix.mul_apply, hinv, Matrix.one_apply]
  simp [apply_ite (algebraMap (Om l) (PadicComplex l))]

theorem kap_idem_mem_inC (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l))
    (K LL : FinExt l) (f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (e : OCO LL)
    (hact : IsActC act) (he : IsIdempotentElem e)
    (hfix : ∀ g ∈ GK K, ∀ k, act g (kap o e k) = kap o e k) (k : Fin f) : kap o e k ∈ inC K.1 := by
  obtain ⟨x, hx⟩ := kap_idem_algebraic o e he k
  refine ⟨x, ?_, hx⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup K.1]
  rintro ⟨g, hg⟩
  have h1 := hfix g hg k
  rw [← hx] at h1
  apply (algebraMap (Om l) (PadicComplex l)).injective
  exact (hact.1 g x).symm.trans h1

end GlobalTheory.Cyc.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenRBaseChangeSubquotient
section
open scoped TensorProduct

namespace GlobalTheory

section

variable {O : Type} [CommRing O] (O' : Type) [CommRing O'] [Algebra O O']
  {W : Type} [AddCommGroup W] [Module O W]

theorem isLatIn_baseChange [IsDomain O'] (hinj : Function.Injective (algebraMap O O'))
    {V L : Submodule O W} (h : Formalism.MainNotions.IntegralHeckeForms.IsLatIn L V) :
    Formalism.MainNotions.IntegralHeckeForms.IsLatIn (L.baseChange O') (V.baseChange O') := by
  obtain ⟨hfg, hle, hsat⟩ := h
  refine ⟨?_, Submodule.baseChange_mono O' hle, ?_⟩
  · obtain ⟨s, rfl⟩ := hfg
    rw [Submodule.baseChange_span]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · intro x hx
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      obtain ⟨c, hc, hcv⟩ := hsat v hv
      refine ⟨algebraMap O O' c, fun h0 => hc (hinj (by rw [h0, map_zero])), ?_⟩
      rw [algebraMap_smul, ← map_smul]
      exact Submodule.tmul_mem_baseChange_of_mem 1 hcv
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, hay⟩ := hy
      obtain ⟨b, hb, hbz⟩ := hz
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hay
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hbz
    | smul a y _ hy =>
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨b, hb, ?_⟩
      rw [smul_comm]
      exact Submodule.smul_mem _ _ hby

variable [IsDomain O] [IsDiscreteValuationRing O] [IsDomain O'] [IsDiscreteValuationRing O']
  [IsLocalHom (algebraMap O O')]

theorem lenR_baseChange_subquotient (hinj : Function.Injective (algebraMap O O')) (l : ℕ)
    (A B : Submodule O W) :
    Formalism.MainNotions.IntegralHeckeForms.lenR O' l
              (A.baseChange O' ⧸ (B.baseChange O').comap (A.baseChange O').subtype) =
      Formalism.MainNotions.IntegralHeckeForms.lenR O l (A ⧸ B.comap A.subtype) := by
  haveI : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').mpr hinj
  have h1 : Module.length O'
      (A.baseChange O' ⧸ (B.baseChange O').comap (A.baseChange O').subtype) =
      Module.length O (A ⧸ B.comap A.subtype) *
        (((IsLocalRing.maximalIdeal O').ramificationIdx O : ℕ) : ℕ∞) :=
    length_baseChange_subquotient_dvr O O' (X := W) A B
  have h2 := addVal_algebraMap (R := O) O' (l : O)
  rw [map_natCast] at h2
  have he : (((IsLocalRing.maximalIdeal O').ramificationIdx O : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ramificationIdx_maximalIdeal_pos O O').ne'
  unfold Formalism.MainNotions.IntegralHeckeForms.lenR
  rw [h1, h2, ENat.toNat_mul, ENat.toNat_mul, ENat.toNat_coe, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_right _ _ he]

end

theorem sIdx_baseChange :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (W : Type) [AddCommGroup W] [Module O W] (l : ℕ) (V L₁ L₂ : Submodule O W), Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₁ V → Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₂ V → Formalism.MainNotions.IntegralHeckeForms.IsLatIn (L₁.baseChange O') (V.baseChange O') ∧ Formalism.MainNotions.IntegralHeckeForms.sIdx l (L₁.baseChange O') (L₂.baseChange O') = Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ := by
  intro O _ _ _ O' _ _ _ _ _ hinj W _ _ l V L₁ L₂ h₁ _
  refine ⟨isLatIn_baseChange O' hinj h₁, ?_⟩
  unfold Formalism.MainNotions.IntegralHeckeForms.sIdx
  rw [lenR_baseChange_subquotient O' hinj, lenR_baseChange_subquotient O' hinj]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCommensurableOfIsLatIn
section
namespace GlobalTheory

open Formalism.MainNotions.IntegralHeckeForms

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W]


variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in
theorem _root_.GlobalTheory.relLength_ne_top_of_isLatIn {V A B : Submodule O W} (hA : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn A V)
    (hB : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn B V) : _root_.GlobalTheory.relLength A B ≠ ⊤ := by
  rw [_root_.GlobalTheory.relLength_ne_top_iff]
  obtain ⟨hAfg, hAV, -⟩ := hA
  obtain ⟨-, -, hBV⟩ := hB
  have : Module.Finite O A := Module.Finite.iff_fg.mpr hAfg
  apply _root_.GlobalTheory.isFiniteLength_of_isTorsion
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    obtain ⟨c, hc, hcB⟩ := hBV a (hAV a.2)
    refine ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hcB


variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in
theorem _root_.GlobalTheory.lengthCommensurable_of_isLatIn {V A B : Submodule O W} (hA : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn A V)
    (hB : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn B V) : _root_.GlobalTheory.LengthCommensurable A B :=
  ⟨_root_.GlobalTheory.relLength_ne_top_of_isLatIn hA hB,
    _root_.GlobalTheory.relLength_ne_top_of_isLatIn hB hA⟩


variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in
theorem _root_.GlobalTheory.sIdx_eq_signedLength_div (l : ℕ) (A B : Submodule O W) :
    _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l A B = (_root_.GlobalTheory.signedLength A B : ℝ) /
      ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℝ) := by
  unfold _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx _root_.Formalism.MainNotions.IntegralHeckeForms.lenR _root_.GlobalTheory.signedLength
  rw [← _root_.GlobalTheory.relLength_eq_length_quotient_comap,
    ← _root_.GlobalTheory.relLength_eq_length_quotient_comap]
  push_cast
  rw [sub_div]


variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in
theorem _root_.GlobalTheory.sIdx_add_and_mono :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (W : Type)
      [AddCommGroup W] [Module O W] (l : ℕ) (V L₁ L₂ L₃ : Submodule O W),
      _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₁ V → _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₂ V → _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₃ V →
      _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃ = _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ + _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₂ L₃ ∧
        (L₃ ≤ L₂ → _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ ≤ _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃) := by
  intro O _ _ _ W _ _ l V L₁ L₂ L₃ h₁ h₂ h₃
  have hadd : _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃ = _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ + _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₂ L₃ := by
    simp only [_root_.GlobalTheory.sIdx_eq_signedLength_div]
    rw [(_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₁ h₂).signedLength_eq_add
      (_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₂ h₃)]
    push_cast
    rw [add_div]
  refine ⟨hadd, fun hle => ?_⟩
  rw [hadd, le_add_iff_nonneg_right, _root_.GlobalTheory.sIdx_eq_signedLength_div]
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact_mod_cast (_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₂ h₃).signedLength_nonneg hle

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmer
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.ResidualSelmer

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → NoChiOff i r Xs → ∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → ∃ η : Fin D.R.nV → KK D.nd i, ∃ γ : GE D.nd, ((yg D.nd r S γ x').map (toK D.nd i)).mulVec η ≠ 0 := by
  intro D i r ρ π Xs S _ hG _ hN x' hx hZ
  have hrank : ((Eel D.nd S x').map (toK D.nd i)).rank = 1 := hG.2.2.2.2.2.2.2.2.2.2.1.1 x'
  by_contra hcon
  push Not at hcon
  have h0 : ∀ η : Fin D.R.nV → KK D.nd i, ((Eel D.nd S x').map (toK D.nd i)).mulVec η = 0 := by
    intro η
    apply hN _ hx hZ
    intro g
    have h := hcon η g
    have hy : yg D.nd r S g x' = rTwO D.nd i r (S.p x') g * Eel D.nd S x' - Eel D.nd S x' := by
      unfold yg
      rw [← Matrix.smul_mul]
      rfl
    rw [hy, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.sub_mulVec, sub_eq_zero,
      ← Matrix.mulVec_mulVec] at h
    exact h
  have hz : ((Eel D.nd S x').map (toK D.nd i)).mulVecLin = 0 := LinearMap.ext h0
  unfold Matrix.rank at hrank
  rw [hz, LinearMap.range_zero, finrank_bot] at hrank
  exact zero_ne_one hrank

end GlobalTheory.Cut.ResidualSelmer
end

