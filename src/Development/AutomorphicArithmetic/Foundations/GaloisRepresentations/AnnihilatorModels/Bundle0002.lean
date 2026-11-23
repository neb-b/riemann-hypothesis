module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAdmExact
section
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem admissible_exact_sequence (hD : DinvExact) {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B]
    (σ : G → End F B) {L : Type} [Field L] [Algebra F L] {e : ℕ} (hB : Bound σ L e)
    {U V W : Type} [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U] [Module.Finite L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] [Module.Finite L V]
    [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W] [Module.Finite L W]
    (ρU : Representation L G U) (ρV : Representation L G V) (ρW : Representation L G W)
    (i : U →ₗ[L] V) (p : V →ₗ[L] W) (hi : Inter ρU ρV i) (hp : Inter ρV ρW p)
    (inj : Function.Injective i) (ex : Function.Exact i p) (surj : Function.Surjective p)
    (hA : admitted σ e ρV) :
    admitted σ e ρU ∧ admitted σ e ρW ∧
      (Dinv σ ρV).map (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) = Dinv σ ρW := by
  obtain ⟨fU, bU⟩ := hB U ρU
  obtain ⟨fV, -⟩ := hB V ρV
  obtain ⟨fW, bW⟩ := hB W ρW
  obtain ⟨hle, hdim⟩ := hD F G B σ L U V W ρU ρV ρW i p hi hp inj ex fV
  have hmono := Submodule.finrank_mono hle
  have hrank : finrank L V = finrank L U + finrank L W := by
    have h1 := LinearMap.finrank_range_add_finrank_ker p
    rw [LinearMap.range_eq_top.mpr surj, finrank_top, LinearMap.exact_iff.mp ex,
      LinearMap.finrank_range_of_inj inj] at h1
    omega
  unfold admitted at hA ⊢
  rw [hrank, mul_add] at hA
  have h2 : finrank L (Dinv σ ρU) = e * finrank L U := by omega
  have h3 : finrank L (Dinv σ ρW) = e * finrank L W := by omega
  refine ⟨h2, h3, Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  omega

theorem UpperTheory.Gal.crystallineComparison.admissibleExact_of_dualInvariantExact :
    DinvExact → AdmExact := by
  intro hD
  unfold AdmExact
  intro F G B _ _ _ _ σ L _ _ e hB V W _ _ _ _ _ _ _ _ _ _ ρ ρ' f hf
  refine ⟨fun inj hA => ?_, fun surj hA => ?_⟩
  · let ρQ : Representation L G (W ⧸ LinearMap.range f) :=
      { toFun := fun g => (LinearMap.range f).mapQ (LinearMap.range f) (ρ' g) (by
          rintro _ ⟨v, rfl⟩
          exact ⟨ρ g v, hf g v⟩)
        map_one' := by
          ext w
          simp
        map_mul' := by
          intro g h
          ext w
          simp [map_mul] }
    have hQ : UpperTheory.Gal.crystallineComparison.Inter ρ' ρQ (LinearMap.range f).mkQ := fun g w => rfl
    exact (admissible_exact_sequence hD σ hB ρ ρ' ρQ f (LinearMap.range f).mkQ hf hQ inj
      (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _) hA).1
  · have hK : ∀ (g : G) (x : LinearMap.ker f), ρ g x ∈ LinearMap.ker f := by
      intro g x
      rw [LinearMap.mem_ker, hf g x, LinearMap.mem_ker.mp x.2, map_zero]
    let ρK : Representation L G (LinearMap.ker f) :=
      { toFun := fun g => LinearMap.codRestrict (LinearMap.ker f)
          ((ρ g).comp (LinearMap.ker f).subtype) (hK g)
        map_one' := by
          ext x
          simp
        map_mul' := by
          intro g h
          ext x
          simp only [map_mul, Module.End.mul_apply]
          rfl }
    have hKi : UpperTheory.Gal.crystallineComparison.Inter ρK ρ (LinearMap.ker f).subtype := fun g x => rfl
    obtain ⟨-, hW, hmap⟩ := admissible_exact_sequence hD σ hB ρK ρ ρ' (LinearMap.ker f).subtype f hKi hf
      (LinearMap.ker f).injective_subtype (LinearMap.exact_subtype_ker_map f) surj hA
    exact ⟨hW, hmap⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAnnExt
section
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.annExt_of :
    DinvExt → AnnExt := by
  intro h F G B _ _ _ _ σ ψ L _ _ V _ _ ρ
  have hD := h F G B σ L V ρ
  have hinj : Function.Injective ((Dinv σ ρ).subtype.baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Dinv σ ρ).injective_subtype
  refine ⟨fun e hadm => ?_, fun q n T hA x hx => ?_⟩
  · unfold admitted at hadm ⊢
    rw [← LinearEquiv.finrank_map_eq (AlgebraTensorModule.assoc F F L L V B), hD, Module.finrank_baseChange]
    rw [← hadm]
    change Module.finrank L (LinearMap.range ((Dinv σ ρ).subtype.baseChange L)) = _
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]
  · unfold AnnD at hA
    dsimp only
    have comm : ∀ (f : V →ₗ[F] V) (g : B →ₗ[F] B) (y : (L ⊗[F] V) ⊗[F] B),
        AlgebraTensorModule.assoc F F L L V B (AlgebraTensorModule.map (f.baseChange L) g y) =
          (AlgebraTensorModule.map f g).lTensor L (AlgebraTensorModule.assoc F F L L V B y) := by
      intro f g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul u b =>
        induction u using TensorProduct.induction_on with
        | zero => simp
        | tmul a v => simp
        | add u₁ u₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add (f := _), h₁, h₂]
      | add y₁ y₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
    have hmem : AlgebraTensorModule.assoc F F L L V B x ∈ (Dinv σ ρ).baseChange L := by
      rw [← hD]
      exact Submodule.mem_map_of_mem hx
    apply (AlgebraTensorModule.assoc F F L L V B).injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero]
    simp only [map_zsmul, comm]
    obtain ⟨z, hz⟩ := Submodule.toBaseChange_surjective' L (Dinv σ ρ) hmem
    rw [← hz]
    clear hz hmem
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a w =>
      simp only [Submodule.coe_toBaseChange_tmul, LinearMap.lTensor_tmul]
      have := hA w w.2
      calc _ = TensorProduct.mk F L (V ⊗[F] B) a (∑ j ∈ Finset.range (n + 1), ((-1) ^ j * (q : ℤ) ^ j.choose 2) • (AlgebraTensorModule.map (T j) (ψ ^ (n - j))) w) := by
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [map_sum, map_zsmul, TensorProduct.mk_apply]
        _ = 0 := by rw [this, map_zero]
    | add z₁ z₂ h₁ h₂ => simp only [map_add (f := _), Submodule.coe_add, Finset.sum_add_distrib, smul_add, h₁, h₂, add_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAnnPer
section
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem algebraTensorModule_map_map_id_left_comm_of_comm {F L V B B' : Type} [Field F] [Field L] [Algebra F L]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    [AddCommGroup B] [Module F B] [AddCommGroup B'] [Module F B']
    (c : B →ₗ[F] B') (f : V →ₗ[L] V) (u : B →ₗ[F] B) (u' : B' →ₗ[F] B')
    (h : ∀ b, c (u b) = u' (c b)) (x : V ⊗[F] B) :
    AlgebraTensorModule.map f u' (AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) c x) =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) c (AlgebraTensorModule.map f u x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.crystallineComparison.annPer_of :
    AnnPer := by
  intro F G B B' _ _ _ _ _ _ σ ψ σ' ψ' c hc hσ hψ L _ _ e hB V _ _ _ _ _ ρ hA
  unfold Bound at hB
  unfold admitted at hA ⊢
  have hpow : ∀ k b, c ((ψ ^ k) b) = (ψ' ^ k) (c b) := by
    intro k
    induction k with
    | zero => intro b; simp
    | succ k ih =>
      intro b
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hψ]
  let m : V ⊗[F] B →ₗ[L] V ⊗[F] B' := AlgebraTensorModule.map LinearMap.id c
  have hm_inj : Function.Injective m := by
    have h1 : ⇑m = ⇑(LinearMap.lTensor V c) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [m]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [h1]
    exact Module.Flat.lTensor_preserves_injective_linearMap c hc
  have hmaps : ∀ x ∈ Dinv σ ρ, m x ∈ Dinv σ' ρ := by
    intro x hx
    simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    exact (algebraTensorModule_map_map_id_left_comm_of_comm c (ρ g) (σ g) (σ' g) (hσ g) x).trans (congrArg m (hx g))
  let φ : Dinv σ ρ →ₗ[L] Dinv σ' ρ := m.restrict hmaps
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply hm_inj
    exact congrArg Subtype.val hab
  obtain ⟨hfin', hle⟩ := hB V ρ
  haveI : Module.Finite L (Dinv σ ρ) := Module.Finite.of_injective φ hφ
  have hge : finrank L (Dinv σ ρ) ≤ finrank L (Dinv σ' ρ) :=
    LinearMap.finrank_le_finrank_of_injective hφ
  have heq : finrank L (Dinv σ ρ) = finrank L (Dinv σ' ρ) := by omega
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hφ
  refine ⟨by omega, ?_⟩
  intro q n T hT
  unfold AnnD at hT ⊢
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have hxy : x = m y.1 := (congrArg Subtype.val hy).symm
  have key : ∀ j, (AlgebraTensorModule.map (T j) (ψ' ^ (n - j))) (m y.1) =
      m ((AlgebraTensorModule.map (T j) (ψ ^ (n - j))) y.1) :=
    fun j => algebraTensorModule_map_map_id_left_comm_of_comm c (T j) (ψ ^ (n - j)) (ψ' ^ (n - j)) (hpow (n - j)) y.1
  have h0 := congrArg m (hT y.1 y.2)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum] at h0
  rw [hxy, ← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [key j]
  exact (LinearMap.map_smul_of_tower m _ _).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAnnSub
section
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem algebraTensorModule_map_map_id_right_comm_of_comm {F L U V B : Type} [Field F] [Field L] [Algebra F L]
    [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    [AddCommGroup B] [Module F B]
    (i : U →ₗ[L] V) (f : U →ₗ[L] U) (f' : V →ₗ[L] V) (u : B →ₗ[F] B)
    (h : ∀ a, i (f a) = f' (i a)) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f' u (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) x) =
      AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) (AlgebraTensorModule.map f u x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.crystallineComparison.annSub_of :
    AnnSub := by
  intro F G B _ _ _ _ σ ψ L _ _ U V _ _ _ _ _ _ _ _ ρU ρ i hI hi q n TU T hT hAnn
  unfold Inter at hI
  unfold AnnD at hAnn ⊢
  let M : U ⊗[F] B →ₗ[L] V ⊗[F] B := AlgebraTensorModule.map i LinearMap.id
  have hM_inj : Function.Injective M := by
    have h1 : ⇑M = ⇑(LinearMap.rTensor B (i.restrictScalars F)) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [M]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [h1]
    exact Module.Flat.rTensor_preserves_injective_linearMap (i.restrictScalars F) hi
  have hpow : ∀ k, ∀ b, (LinearMap.id : B →ₗ[F] B) ((ψ ^ k) b) = (ψ ^ k) ((LinearMap.id : B →ₗ[F] B) b) :=
    fun _ _ => rfl
  intro x hx
  have hmx : M x ∈ Dinv σ ρ := by
    simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    exact (algebraTensorModule_map_map_id_right_comm_of_comm i (ρU g) (ρ g) (σ g) (hI g) x).trans (congrArg M (hx g))
  apply hM_inj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, ← hAnn (M x) hmx, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul_of_tower]
  congr 1
  exact (algebraTensorModule_map_map_id_right_comm_of_comm i (TU j) (T j) (ψ ^ (n - j)) (hT j) x).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PBaseChart
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.baseChart_of :
    BaseOfSmooth → BaseOfChart := by
  intro h
  unfold BaseOfChart
  intro l O _ _ _ ϖ hϖ hl hlu Y g hg U hU
  let φ : O →+* Γ(Y, U) :=
    (g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hφ : ∀ a : O, φ a = (Y.presheaf.map (homOfLE le_top).op).hom
      ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) := fun a => rfl
  have hsm : φ.Smooth := by
    refine RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_) ?_
    · exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv)
    · exact HasRingHomProperty.appLE @Smooth g hg ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  letI : Algebra O Γ(Y, U) := φ.toAlgebra
  haveI : Algebra.Smooth O Γ(Y, U) := hsm
  have hb := h l O Γ(Y, U) ϖ hϖ hl hlu
  have hϖφ : (algebraMap O Γ(Y, U)) ϖ = (Y.presheaf.map (homOfLE le_top).op).hom (fn g ϖ) := hφ ϖ
  rw [hϖφ] at hb
  refine ⟨hb, 1, ?_⟩
  have hmem : (l : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hlu
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [pow_one, ← hϖφ, Ideal.mem_span_singleton']
  refine ⟨algebraMap O Γ(Y, U) c, ?_⟩
  rw [← map_mul, hc, map_natCast]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PBaseSmooth
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.baseSmooth_of :
    SmoothClosed → SmoothReduced → BaseOfSmooth := by
  intro hC hR l O R _ _ _ _ _ _ ϖ hϖ hl _
  have hflat : Module.Flat O R := Algebra.Smooth.flat O R
  have hlO : (l : O) ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero hl
  refine ⟨?_, hC l O R hl, ?_⟩
  · have hreg : IsSMulRegular R (l : O) := Module.Flat.isSMulRegular_of_nonZeroDivisors hlO
    have key : ∀ x : R, (l : R) * x = 0 → x = 0 := by
      intro x hx
      apply hreg
      simp only [Algebra.smul_def, map_natCast, mul_zero]
      exact hx
    rw [mem_nonZeroDivisors_iff]
    exact ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩
  · rw [Ideal.isRadical_iff_quotient_reduced]
    have hspan : Ideal.span {(algebraMap O R) ϖ} = (IsLocalRing.maximalIdeal O).map (algebraMap O R) := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span, Set.image_singleton]
    rw [hspan]
    haveI : Algebra.Smooth (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] R) :=
      Algebra.Smooth.baseChange O R (IsLocalRing.ResidueField O)
    have hred : IsReduced (IsLocalRing.ResidueField O ⊗[O] R) :=
      hR (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] R)
    haveI : IsReduced ((O ⧸ IsLocalRing.maximalIdeal O) ⊗[O] R) := hred
    let e := ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (IsLocalRing.maximalIdeal O)).restrictScalars O).trans
      (Algebra.TensorProduct.comm O R (O ⧸ IsLocalRing.maximalIdeal O))
    exact isReduced_of_injective e.toRingHom e.injective
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCharAnn
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.charAnn_of :
    CharOfAnn := by
  intro K _ n M s hcard hgen hann hdet
  classical
  set L := AlgebraicClosure K
  set f : K →+* L := algebraMap K L
  have hf : Function.Injective f := f.injective
  set M' : Matrix (Fin n) (Fin n) L := M.map f
  have hchar : M'.charpoly = M.charpoly.map f := Matrix.charpoly_map M f
  have hpmap : (rootPol s).map f = (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (s.map f)).prod := by
    simp [rootPol, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def]
  have hannL : Polynomial.aeval M' (rootPol s) = 0 := by
    have h1 : M' = (Algebra.ofId K L).mapMatrix M := by
      rw [AlgHom.mapMatrix_apply]; rfl
    rw [h1, Polynomial.aeval_algHom_apply, hann, map_zero]
  set R := M'.charpoly.roots
  have hmem : ∀ r ∈ R, r ∈ s.map f := by
    intro r hr
    have hroot : M'.charpoly.IsRoot r := (Polynomial.mem_roots (Matrix.charpoly_monic M').ne_zero).1 hr
    have hsp : r ∈ spectrum L M' := Matrix.mem_spectrum_of_isRoot_charpoly hroot
    have hev : Polynomial.eval r ((rootPol s).map f) ∈ spectrum L (Polynomial.aeval M' ((rootPol s).map f)) :=
      spectrum.subset_polynomial_aeval M' _ ⟨r, hsp, rfl⟩
    have hz : Polynomial.aeval M' ((rootPol s).map f) = 0 := by
      rw [Polynomial.aeval_map_algebraMap]; exact hannL
    rw [hz] at hev
    have h0 : Polynomial.eval r ((rootPol s).map f) = 0 := by
      by_contra hne
      exact (spectrum.mem_iff.1 hev) (by
        simpa using (isUnit_iff_ne_zero.2 hne).map (algebraMap L (Matrix (Fin n) (Fin n) L)))
    have hne0 : (rootPol s).map f ≠ 0 := by
      rw [hpmap]; exact (Polynomial.monic_multiset_prod_of_monic _ _ (fun a _ => Polynomial.monic_X_sub_C a)).ne_zero
    have : r ∈ ((rootPol s).map f).roots := (Polynomial.mem_roots hne0).2 h0
    rwa [hpmap, Polynomial.roots_multiset_prod_X_sub_C] at this
  set g := Function.invFun f
  set t := R.map g
  have htR : t.map f = R := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id R]
    apply Multiset.map_congr rfl
    intro r hr
    obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 (hmem r hr)
    exact Function.invFun_eq ⟨a, ha⟩
  have hRcard : R.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have htcard : t.card = s.card := by simp [t, hRcard, hcard]
  have htsub : ∀ x ∈ t, x ∈ s := by
    intro x hx
    have : f x ∈ s.map f := hmem (f x) (by rw [← htR]; exact Multiset.mem_map_of_mem f hx)
    obtain ⟨a, ha, hax⟩ := Multiset.mem_map.1 this
    rw [← hf hax]; exact ha
  have htprod : t.prod = s.prod := by
    apply hf
    rw [map_multiset_prod, htR, ← Matrix.det_eq_prod_roots_charpoly, ← hdet, RingHom.map_det]
    rfl
  have hts : t = s := hgen t htcard htsub htprod
  apply Polynomial.map_injective f hf
  rw [← hchar, hpmap, ← hts, htR]
  exact (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic M')
    (by rw [IsAlgClosed.card_roots_eq_natDegree])).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCharts
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.charts_of :
    ChartsExist := by
  intro l Y hY J _ T y
  haveI : ∀ j, IsFinite (T j).p := fun j => (T j).fin
  let S : Set Y := {y} ∪ ⋃ j, (T j).r '' ((T j).p ⁻¹' {y})
  have hS : S.Finite := (Set.finite_singleton y).union
    (Set.finite_iUnion fun j => ((T j).p.finite_preimage_singleton y).image _)
  obtain ⟨V, hV, hSV⟩ := hY hS.toFinset
  have hSV' : ∀ x ∈ S, x ∈ V := fun x hx => hSV x (hS.mem_toFinset.mpr hx)
  have hclosed : IsClosed (⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ) :=
    isClosed_iUnion_of_finite fun j => (T j).p.isClosedMap _ ((T j).r ⁻¹ᵁ V).isOpen.isClosed_compl
  let O : Y.Opens := ⟨(⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ)ᶜ, hclosed.isOpen_compl⟩
  have hyO : y ∈ O := by
    show y ∈ (⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ)ᶜ
    rintro hy
    obtain ⟨j, z, hz, hzy⟩ := Set.mem_iUnion.mp hy
    apply hz
    show (T j).r z ∈ V
    exact hSV' _ (Or.inr (Set.mem_iUnion.mpr ⟨j, z, hzy, rfl⟩))
  obtain ⟨U, hU, hyU, hUO⟩ := exists_isAffineOpen_mem_and_subset hyO
  refine ⟨U, V, hU, hV, hyU, fun j z hz => ?_⟩
  by_contra h
  have hz' : (T j).p z ∈ (O : Set Y) := hUO hz
  exact hz' (Set.mem_iUnion.mpr ⟨j, z, h, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCoeffInt
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.coeffInt_of :
    CoeffInt := by
  intro R T _ _ _ ι I _ _ c hc a m
  let c' : I → ι → integralClosure R T := fun i k => ⟨c i k, hc i k⟩
  let f : MvPolynomial ι (integralClosure R T) →+* MvPolynomial ι T :=
    MvPolynomial.map (algebraMap (integralClosure R T) T)
  have hform : ∀ i, form (c i) = (form (c' i)).map f := by
    intro i
    simp [form, f, Polynomial.map_sub, MvPolynomial.map_C, c']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.map_sum]
    simp [Polynomial.map_mul, Polynomial.map_C, MvPolynomial.map_C, MvPolynomial.map_X]
  have hP : (∏ i, form (c i)) = (∏ i, form (c' i)).map f := by
    rw [Polynomial.map_prod]
    exact Finset.prod_congr rfl fun i _ => hform i
  rw [hP, Polynomial.coeff_map]
  simp only [f, MvPolynomial.coeff_map]
  exact (((∏ i, form (c' i)).coeff a).coeff m).2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetSplit
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detSplit_of :
    DetSplit := by
  intro A _ m I _ _ P Q hPQ d
  have h1 : 1 - Q * P + Q * Matrix.diagonal d * P = 1 + Q * ((Matrix.diagonal d - 1) * P) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, ← Matrix.mul_assoc]
    abel
  rw [h1, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hPQ, Matrix.mul_one, add_sub_cancel,
    Matrix.det_diagonal]
end

