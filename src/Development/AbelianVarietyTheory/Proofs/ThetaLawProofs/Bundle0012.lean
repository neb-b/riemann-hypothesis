module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsResEqOfUnitInChart

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

noncomputable def holUnifReparam {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → ℂ) (he : Differentiable ℂ e) (hne : ∀ z, e z ≠ 0) :
    HolUnif A L g where
  ex z := u.ex (φ z)
  ex_add z w := by rw [map_add (f := _), u.ex_add]
  ex_onto := u.ex_onto.comp φ.surjective
  Λ := u.Λ.comap (φ.toLinearMap.restrictScalars ℤ)
  ker z := u.ker (φ z)
  discrete := by
    haveI := u.discrete
    have hc : Continuous (fun z : Fin g → ℂ => φ z) := φ.toContinuousLinearEquiv.continuous
    refine DiscreteTopology.of_continuous_injective
      (f := fun x : u.Λ.comap (φ.toLinearMap.restrictScalars ℤ) => (⟨φ x.1, x.2⟩ : u.Λ))
      ((hc.comp continuous_subtype_val).subtype_mk _) ?_
    intro x y h
    exact Subtype.ext (φ.injective (congrArg Subtype.val h))
  full := by
    have h1 : ((u.Λ.comap (φ.toLinearMap.restrictScalars ℤ) : Submodule ℤ (Fin g → ℂ)) : Set (Fin g → ℂ)) =
        (φ.symm.toLinearMap.restrictScalars ℝ) '' (u.Λ : Set (Fin g → ℂ)) := by
      ext z
      constructor
      · intro hz
        exact ⟨φ z, hz, φ.symm_apply_apply z⟩
      · rintro ⟨w, hw, rfl⟩
        show φ (φ.symm w) ∈ u.Λ
        rwa [φ.apply_symm_apply]
    rw [h1, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.symm.surjective
  hol U f := by
    have hc : Differentiable ℂ (fun z : Fin g → ℂ => φ z) := φ.toContinuousLinearEquiv.differentiable
    exact ⟨(u.hol U f).1.preimage hc.continuous, (u.hol U f).2.comp hc.differentiableOn (fun _ hz => hz)⟩
  fr i z := u.fr i (φ z) / e z
  fr_hol i := by
    have hc : Differentiable ℂ (fun z : Fin g → ℂ => φ z) := φ.toContinuousLinearEquiv.differentiable
    have h1 : DifferentiableOn ℂ (fun z => u.fr i (φ z)) {z | ⊤ ≤ (u.ex (φ z)).left ⁻¹ᵁ L.U i} :=
      (u.fr_hol i).comp hc.differentiableOn (fun _ hz => hz)
    have h2 : Differentiable ℂ (fun z => (e z)⁻¹) := he.inv hne
    simp only [div_eq_mul_inv]
    exact h1.mul h2.differentiableOn
  fr_ne i z hz := div_ne_zero (u.fr_ne i _ hz) (hne z)
  fr_compat i j z hz := by
    rw [u.fr_compat i j _ hz, mul_div_assoc]

theorem exists_holUnif_reparam :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → ℂ), Differentiable ℂ e → (∀ z, e z ≠ 0) → e 0 = 1 → ∃ u' : HolUnif A L g, (∀ z, u'.ex z = u.ex (φ z)) ∧ (∀ z, z ∈ u'.Λ ↔ φ z ∈ u.Λ) ∧ (∀ rig, u.IsRig rig → u'.IsRig rig) ∧ (∀ s θ, u.IsFn s θ → u'.IsFn s (fun z => e z * θ (φ z))) ∧ ∀ w v, u.IsDiff (φ w) v → u'.IsDiff w v := by
  intro A _ L g u φ e he hne h0
  refine ⟨holUnifReparam u φ e he hne, fun _ => rfl, fun _ => Iff.rfl, ?_, ?_, ?_⟩
  · intro rig hr j hj
    show u.fr _ (φ 0) / e 0 = _
    rw [map_zero, h0, div_one]
    exact hr j hj
  · intro s θ hs i z hz
    have h := hs i (φ z) hz
    show valAt' (u.ex (φ z)).left _ _ = e z * θ (φ z) * (u.fr i (φ z) / e z)
    rw [h]
    have := hne z
    field_simp
  · intro w v hv U h f
    rw [hv U h f]
    have key := φ.toContinuousLinearEquiv.comp_right_fderiv
      (f := fun z => valAt' (u.ex z).left U f) (x := 0)
    have h2 := congrArg (fun T => T w) key
    simp only [map_zero] at h2
    exact h2.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FormallySmoothQuotient
section
noncomputable section
namespace GlobalTheory.HenselZero

open IsLocalRing GlobalTheory.SqZero

theorem formallySmooth_quotient {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    [Fintype ι] [DecidableEq ι] (f : ι → S) (τ : ι → Derivation R S S)
    (h : IsUnit (Matrix.of fun i k => τ k (f i)).det) :
    Algebra.FormallySmooth R (S ⧸ Ideal.span (Set.range f)) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI g => ?_
  obtain ⟨g', hg'⟩ := Algebra.FormallySmooth.comp_surjective R S I hI (g.comp (Ideal.Quotient.mkₐ R _))
  have hg : ∀ a, Ideal.Quotient.mk I (g' a) = g (Ideal.Quotient.mk _ a) := fun a => congr($hg' a)
  have hf : ∀ i, g' (f i) ∈ I := fun i => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hg, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self i)), map_zero]
  let M : Matrix ι ι B := Matrix.of fun i k => g' (τ k (f i))
  have hM : IsUnit M.det := by
    have := h.map g'
    rw [AlgHom.map_det] at this
    exact this
  let t : ι → B := M⁻¹.mulVec fun i => - g' (f i)
  have ht : ∀ k, t k ∈ I := fun k => Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (neg_mem (hf i))
  have hMt : M.mulVec t = fun i => - g' (f i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
  have h0 : ∀ i j, t i * t j = 0 := fun i j => by
    have := Ideal.mul_mem_mul (ht i) (ht j)
    rwa [← sq, hI] at this
  refine ⟨Ideal.Quotient.liftₐ _ (addDers τ g' t h0) fun a ha => ?_, ?_⟩
  · refine (Ideal.span_le (I := RingHom.ker (addDers τ g' t h0))).2 ?_ ha
    rintro _ ⟨i, rfl⟩
    have : ∑ k, g' (τ k (f i)) * t k = - g' (f i) := congrFun hMt i
    show addDers τ g' t h0 (f i) = 0
    rw [addDers_apply, this, add_neg_cancel]
  · refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun a => ?_)
    show Ideal.Quotient.mk I (addDers τ g' t h0 a) = g (Ideal.Quotient.mk _ a)
    rw [addDers_apply, map_add (f := _), hg, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (ht k)), add_zero]

theorem exists_derivation_lift {R S K : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    [CommRing K] [Algebra R K] (u : S →ₐ[R] K) (hu : Function.Surjective u) (D : S →ₗ[R] K)
    (hD : ∀ a b, D (a * b) = u a * D b + u b * D a) : ∃ τ : Derivation R S S, ∀ a, u (τ a) = D a := by
  let _ : Algebra S K := (u : S →+* K).toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq fun r => (u.commutes r).symm
  let D' : Derivation R S K := Derivation.mk' D hD
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (Algebra.linearMap S K) D'.liftKaehlerDifferential hu
  refine ⟨l.compDer (KaehlerDifferential.D R S), fun a => ?_⟩
  exact (congr($hl (KaehlerDifferential.D R S a))).trans (D'.liftKaehlerDifferential_comp_D a)

theorem exists_algHom_ker_eq {O S ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra O S]
    [Algebra.FormallySmooth O S] [Fintype ι] [DecidableEq ι] (f : ι → S) (u : S →+* ResidueField O)
    (hu : ∀ r, u (algebraMap O S r) = residue O r) (hf : ∀ i, u (f i) = 0)
    (χ : ι → (S →+* DualNumber (ResidueField O))) (h₁ : ∀ k a, (χ k a).fst = u a)
    (h₂ : ∀ k r, χ k (algebraMap O S r) = algebraMap (ResidueField O) _ (residue O r))
    (hd : (Matrix.of fun i k => (χ k (f i)).snd).det ≠ 0)
    (hm : maximalIdeal S ≤ Ideal.span (Set.range f) ⊔ (maximalIdeal O).map (algebraMap O S)) :
    ∃ ψ : S →ₐ[O] O, (∀ a, residue O (ψ a) = u a) ∧ RingHom.ker ψ = Ideal.span (Set.range f) := by
  let u' : S →ₐ[O] ResidueField O := ⟨u, hu⟩
  have hs : Function.Surjective u' := fun c => by
    obtain ⟨r, rfl⟩ := residue_surjective c
    exact ⟨_, hu r⟩
  have hker : RingHom.ker u = maximalIdeal S := eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective u hs)
  have hτ : ∀ k, ∃ τ : Derivation O S S, ∀ a, u (τ a) = (χ k a).snd := fun k =>
    exists_derivation_lift u' hs
      { toFun := fun a => (χ k a).snd
        map_add' := fun a b => by simp
        map_smul' := fun r a => by
          rw [Algebra.smul_def, map_mul, h₂, Algebra.smul_def]
          simp [TrivSqZeroExt.algebraMap_eq_inl] }
      fun a b => by simp [h₁, mul_comm]; rfl
  choose τ hτ using hτ
  have hunit : IsUnit (Matrix.of fun i k => τ k (f i)).det := by
    rw [← notMem_maximalIdeal, ← hker, RingHom.mem_ker, RingHom.map_det]
    refine fun h => hd (Eq.trans ?_ h)
    congr 1
    ext i k
    exact (hτ k _).symm
  have := formallySmooth_quotient f τ hunit
  have hle : Ideal.span (Set.range f) ≤ RingHom.ker u' := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hf i)
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := maximalIdeal O)
    (Ideal.Quotient.liftₐ (Ideal.span (Set.range f)) u' fun a ha => hle ha)
  let ψ : S →ₐ[O] O := g.comp (Ideal.Quotient.mkₐ O _)
  have hψ : ∀ a, residue O (ψ a) = u a := fun a => congr($hg (Ideal.Quotient.mk _ a))
  have hle' : Ideal.span (Set.range f) ≤ RingHom.ker ψ := fun a ha => by
    show g (Ideal.Quotient.mk _ a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  refine ⟨ψ, hψ, le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal S)
    (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _) fun a ha => ?_) hle'⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have ha₀ : ψ a = 0 := ha
  have ha' : a ∈ maximalIdeal S := by rw [← hker, RingHom.mem_ker, ← hψ, ha₀, map_zero]
  replace ha' := hm ha'
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at ha'
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 ha'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hc
  refine Submodule.add_mem_sup hb (Submodule.smul_mem_smul (r := algebraMap O S π) (n := c) ?_ ?_)
  · rw [← hker, RingHom.mem_ker, hu, residue_eq_zero_iff]
    exact hπ.not_isUnit
  · have hb₀ : ψ b = 0 := hle' hb
    rw [map_add (f := _), hb₀, zero_add, map_mul, AlgHom.commutes] at ha₀
    exact (mul_eq_zero.1 ha₀).resolve_left hπ.ne_zero

end GlobalTheory.HenselZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieCombIffProd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PowLie

variable {R : Type} [CommRing R]

def sc (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])

def zeroPt (R : Type) [CommRing R] : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.PowLie.isTangent_iff {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G]
    (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent w ↔ _root_.GlobalTheory.PowLie.zeroPt R ≫ w = η[G] := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent
  constructor
  · intro h
    ext
    simpa [_root_.GlobalTheory.PowLie.zeroPt] using h
  · intro h
    simpa [_root_.GlobalTheory.PowLie.zeroPt] using congrArg Over.Hom.left h

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.PowLie.isLieComb_iff_prod {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G] [IsCommMonObj G]
    {n : ℕ} (c : Fin n → R) (v : Fin n → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G)) (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb c v w ↔ w = ∏ i, _root_.GlobalTheory.PowLie.sc (c i) ≫ v i := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    ext
    simp [_root_.GlobalTheory.PowLie.sc, hu i]
  · intro hw
    refine ⟨fun i => _root_.GlobalTheory.PowLie.sc (c i) ≫ v i, fun i => by
      simp [_root_.GlobalTheory.PowLie.sc], ?_⟩
    rw [List.prod_ofFn]
    exact hw

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
private theorem finset_prod_comp_of_isMonHom {X M N : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [MonObj M] [IsCommMonObj M]
    [MonObj N] [IsCommMonObj N] {κ : Type*} (s : Finset κ) (f : κ → (X ⟶ M)) (h : M ⟶ N)
    [IsMonHom h] : (∏ i ∈ s, f i) ≫ h = ∏ i ∈ s, f i ≫ h :=
  map_prod (IsMonHom.monoidHom h X) f s

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
private theorem zeroPt_comp_one {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G] :
    _root_.GlobalTheory.PowLie.zeroPt R ≫ (1 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) = η[G] := by
  rw [comp_one, Hom.one_def]
  simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.PowLie.isLieBasis_pow : ∀ (R : Type) [CommRing R] (G' G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) [GrpObj G']
    [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j g : ℕ) (p : _root_.ReciprocityTheory.ChartRestriction.G.Out.IsPowGrp G' G j)
    (v : Fin g → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v → ∃ v' : Fin (j * g) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G'),
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v' ∧ ∀ (i i' : Fin j) (k : Fin g),
        v' (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 := by
  intro R _ G' G _ _ _ _ j g p v hv
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis at hv ⊢
  obtain ⟨htan, huniq⟩ := hv
  have hmon : ∀ i, IsMonHom (p.pr i) := p.hom
  let v' : Fin (j * g) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G') := fun m =>
    Fan.IsLimit.lift p.lim (fun i' =>
      if (finProdFinEquiv.symm m).1 = i' then v (finProdFinEquiv.symm m).2 else 1)
  have hv' : ∀ (i i' : Fin j) (k : Fin g),
      v' (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 := by
    intro i i' k
    exact (Fan.IsLimit.fac p.lim _ i').trans (by simp only [Equiv.symm_apply_apply])
  have hpr : ∀ (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G') (i : Fin j), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent w → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent (w ≫ p.pr i) := by
    intro w i hw
    rw [_root_.GlobalTheory.PowLie.isTangent_iff] at hw ⊢
    rw [← Category.assoc, hw, IsMonHom.one_hom]
  have hcomb : ∀ (c : Fin (j * g) → R) (i' : Fin j),
      (∏ m, _root_.GlobalTheory.PowLie.sc (c m) ≫ v' m) ≫ p.pr i' =
        ∏ k, _root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i', k))) ≫ v k := by
    intro c i'
    rw [finset_prod_comp_of_isMonHom, ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
    have hterm : ∀ (i : Fin j) (k : Fin g),
        (_root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i, k))) ≫ v' (finProdFinEquiv (i, k))) ≫
            p.pr i' =
          if i = i' then _root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i, k))) ≫ v k else 1 := by
      intro i k
      rw [Category.assoc, hv']
      split_ifs <;> simp [comp_one]
    simp only [hterm]
    rw [Fintype.prod_eq_single i' (fun i hi => by simp [hi])]
    simp
  refine ⟨v', ⟨fun m => ?_, fun w hw => ?_⟩, hv'⟩
  · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
    rw [_root_.GlobalTheory.PowLie.isTangent_iff]
    refine Fan.IsLimit.hom_ext p.lim _ _ fun i' => ?_
    change (_root_.GlobalTheory.PowLie.zeroPt R ≫ v' (finProdFinEquiv (i, k))) ≫ p.pr i' =
      η[G'] ≫ p.pr i'
    rw [Category.assoc, hv', IsMonHom.one_hom]
    split_ifs
    · exact (_root_.GlobalTheory.PowLie.isTangent_iff _).1 (htan k)
    · exact zeroPt_comp_one
  · choose cc hcc hcc' using fun i => huniq (w ≫ p.pr i) (hpr w i hw)
    refine ⟨fun m => cc (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2, ?_, ?_⟩
    · beta_reduce
      rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod]
      refine Fan.IsLimit.hom_ext p.lim _ _ fun i' => ?_
      change w ≫ p.pr i' = (∏ m, _) ≫ p.pr i'
      rw [hcomb, (_root_.GlobalTheory.PowLie.isLieComb_iff_prod _ _ _).1 (hcc i')]
      simp
    · intro c' hc'
      rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod] at hc'
      funext m
      obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
      have h := hcc' i (fun k => c' (finProdFinEquiv (i, k))) (by
        beta_reduce
        rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod, hc', hcomb])
      simpa using congrFun h k

end GlobalTheory.PowLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusProdSec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxSection

theorem res_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : W ≤ V) (a : Γ(X, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (h : U' ≤ U)
    (e : W ≤ f ⁻¹ᵁ U') (e' : W ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE U' W e).hom ((X.presheaf.map (homOfLE h).op).hom a) = (f.appLE U W e').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

noncomputable def prodSec {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (t : K → L.Sec) : (LB.LinComb L φ (fun _ => 1)).Sec where
  f jj := ∏ i, ((φ i).appLE _ (LB.wchart L φ jj) (LB.wchart_le L φ jj i)).hom ((t i).f (jj i))
  compat jj jj' := by
    have hg : @Units.val Γ(Y, LB.wchart L φ jj ⊓ LB.wchart L φ jj') _
        ((LB.LinComb L φ (fun _ => 1)).g jj jj') =
        ∏ i, ((φ i).appLE (L.U (jj i) ⊓ L.U (jj' i)) (LB.wchart L φ jj ⊓ LB.wchart L φ jj')
          (le_inf (inf_le_left.trans (LB.wchart_le L φ jj i))
            (inf_le_right.trans (LB.wchart_le L φ jj' i)))).hom (L.g (jj i) (jj' i) : Γ(X, _)) := by
      simp only [LB.LinComb, zpow_one, Units.coe_prod]
      rfl
    change (Y.presheaf.map (homOfLE (inf_le_left :
        LB.wchart L φ jj ⊓ LB.wchart L φ jj' ≤ LB.wchart L φ jj)).op).hom (∏ i, _) =
      @Units.val Γ(Y, LB.wchart L φ jj ⊓ LB.wchart L φ jj') _
        ((LB.LinComb L φ (fun _ => 1)).g jj jj') *
      (Y.presheaf.map (homOfLE (inf_le_right :
        LB.wchart L φ jj ⊓ LB.wchart L φ jj' ≤ LB.wchart L φ jj')).op).hom (∏ i, _)
    rw [hg, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have e := congrArg ((φ i).appLE (L.U (jj i) ⊓ L.U (jj' i)) (LB.wchart L φ jj ⊓ LB.wchart L φ jj')
          (le_inf (inf_le_left.trans (LB.wchart_le L φ jj i))
            (inf_le_right.trans (LB.wchart_le L φ jj' i)))).hom ((t i).compat (jj i) (jj' i))
    rw [map_mul] at e
    refine (res_appLE _ _ _ _).trans (((appLE_res _ _ _ _ _).symm.trans e).trans ?_)
    congr 1
    exact (appLE_res _ _ _ _ _).trans (res_appLE _ _ _ _).symm

theorem mem_basicOpen_prod {Y : Scheme.{0}} {K : Type} [Fintype K] {W : Y.Opens} (a : K → Γ(Y, W))
    {y : Y} (hy : y ∈ W) (h : ∀ i, y ∈ Y.basicOpen (a i)) : y ∈ Y.basicOpen (∏ i, a i) := by
  rw [Scheme.mem_basicOpen _ _ y hy, map_prod]
  exact IsUnit.prod_univ_iff.2 fun i => (Scheme.mem_basicOpen _ _ y hy).1 (h i)

theorem mem_nonzeroLocus_prodSec {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (t : K → L.Sec) (y : Y) (h : ∀ i, φ i y ∈ Out.nonzeroLocus (t i)) :
    y ∈ Out.nonzeroLocus (prodSec L φ t) := by
  choose k hk using fun i => TopologicalSpace.Opens.mem_iSup.1 (h i)
  have hy : y ∈ LB.wchart L φ k := Set.mem_iInter.2 fun i => X.basicOpen_le _ (hk i)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_basicOpen_prod _ hy fun i => ?_⟩
  exact (Scheme.basicOpen_appLE (φ i) _ _ (LB.wchart_le L φ k i) _).ge ⟨hy, hk i⟩

theorem exists_point_powObj {S : Scheme.{0}} (G : Over S) (s : S) :
    ∀ (n : ℕ) (x : Fin n → G.left), (∀ i, G.hom (x i) = s) →
      ∃ y : (Out.powObj G n).left, (Out.powObj G n).hom y = s ∧
        ∀ i, (Out.powPr G i).left y = x i := by
  intro n
  induction n with
  | zero =>
    intro _ _
    exact ⟨s, rfl, fun i => i.elim0⟩
  | succ n ih =>
    intro x hx
    obtain ⟨z, hz, hz'⟩ := ih (fun i => x i.succ) (fun i => hx i.succ)
    obtain ⟨y, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom)
      (g := (Out.powObj G n).hom) (x 0) z ((hx 0).trans hz.symm)
    refine ⟨y, ?_, fun i => Fin.cases ?_ (fun i => ?_) i⟩
    · change G.hom (pullback.fst G.hom (Out.powObj G n).hom y) = s
      rw [h1, hx]
    · exact h1
    · change (Out.powPr G i).left (pullback.snd G.hom (Out.powObj G n).hom y) = _
      rw [h2, hz']

theorem exists_point {S : Scheme.{0}} {G' G : Over S} {n : ℕ} (pr : Fin n → (G' ⟶ G))
    (lim : IsLimit (Fan.mk G' pr)) (s : S) (x : Fin n → G.left) (hx : ∀ i, G.hom (x i) = s) :
    ∃ y : G'.left, G'.hom y = s ∧ ∀ i, (pr i).left y = x i := by
  obtain ⟨z, hz, hz'⟩ := exists_point_powObj G s n x hx
  let m : Out.powObj G n ⟶ G' := lim.lift (Fan.mk (Out.powObj G n) (Out.powPr G (n := n)))
  have hm : ∀ i, m ≫ pr i = Out.powPr G i := fun i => lim.fac _ ⟨i⟩
  refine ⟨m.left z, ?_, fun i => ?_⟩
  · rw [← Scheme.Hom.comp_apply, Over.w m, hz]
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hm, hz']

theorem exists_boxSec : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : Out.IsPowGrp G' G j) (L : LB G.left) (t : Fin j → L.Sec), L.IsLB → ∃ t' : (Out.boxLB L p.pr).Sec, (∀ (jj : Fin j → L.ι) (h : ∀ i, (Out.boxLB L p.pr).U jj ≤ (p.pr i).left ⁻¹ᵁ L.U (jj i)), t'.f jj = ∏ i, ((p.pr i).left.appLE _ _ (h i)).hom ((t i).f (jj i))) ∧ ∀ s : S, (∀ i, ∃ x : G.left, G.hom x = s ∧ x ∈ Out.nonzeroLocus (t i)) → ∃ y : G'.left, G'.hom y = s ∧ y ∈ Out.nonzeroLocus t' := by
  intro S G' G _ _ j p L t _
  refine ⟨prodSec L (fun i => (p.pr i).left) t, fun _ _ => rfl, fun s hs => ?_⟩
  choose x hx hx' using hs
  obtain ⟨y, hy, hy'⟩ := exists_point p.pr p.lim s x hx
  exact ⟨y, hy, mem_nonzeroLocus_prodSec L _ t y fun i => (hy' i).symm ▸ hx' i⟩

end GlobalTheory.BoxSection
end

