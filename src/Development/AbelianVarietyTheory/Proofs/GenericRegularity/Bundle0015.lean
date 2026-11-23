module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.Reg.VecEig

open GlobalTheory.GrpTangent

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def comb {n : ℕ} (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R) : epsR R ⟶ G :=
  ∏ i, epsScale (c i) ≫ v i

theorem isLieComb_iff_comb {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = comb v c := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    apply Over.OverMorphism.ext
    rw [hu i, Over.comp_left]
    rfl
  · rintro rfl
    refine ⟨fun i => epsScale (c i) ≫ v i, fun i => ?_, ?_⟩
    · rw [Over.comp_left]
      rfl
    · rw [List.prod_ofFn]
      rfl

theorem comp_finProd {X Y : Over (Sp R)} (g : X ⟶ Y) {κ : Type} (s : Finset κ) (u : κ → (Y ⟶ G)) :
    g ≫ ∏ i ∈ s, u i = ∏ i ∈ s, g ≫ u i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact Chart.comp_one' g
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, comp_mul, ih]

theorem finProd_comp {X : Over (Sp R)} (g : G ⟶ G) [IsMonHom g] {κ : Type} (s : Finset κ) (u : κ → (X ⟶ G)) :
    (∏ i ∈ s, u i) ≫ g = ∏ i ∈ s, u i ≫ g := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact one_comp g
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_comp, ih]

theorem epsScale_sum_comp {w : epsR R ⟶ G} (hw : IsTangent w) {κ : Type} (s : Finset κ) (a : κ → R) :
    epsScale (∑ i ∈ s, a i) ≫ w = ∏ i ∈ s, epsScale (a i) ≫ w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.prod_empty]
    exact epsScale_zero_comp hw
  · intro b t hb ih
    rw [Finset.sum_insert hb, Finset.prod_insert hb, epsScale_add_comp _ _ hw, ih]

theorem epsScale_comb {n : ℕ} (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R) (z : R) :
    epsScale z ≫ comb v c = comb v (z • c) := by
  unfold comb
  rw [comp_finProd]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Category.assoc, epsScale_mul, Pi.smul_apply, smul_eq_mul]

theorem comb_comp {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (g : G ⟶ G) [IsMonHom g]
    (A : Matrix (Fin n) (Fin n) R) (hA : ∀ j, v j ≫ g = comb v fun i => A i j) (c : Fin n → R) :
    comb v c ≫ g = comb v (A.mulVec c) := by
  calc comb v c ≫ g = ∏ j, (epsScale (c j) ≫ v j) ≫ g := finProd_comp g _ _
    _ = ∏ j, comb v (c j • fun i => A i j) :=
        Finset.prod_congr rfl fun j _ => by rw [Category.assoc, hA j, epsScale_comb]
    _ = ∏ j, ∏ i, epsScale (A i j * c j) ≫ v i := Finset.prod_congr rfl fun j _ => by
        unfold comb
        exact Finset.prod_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm (c j)]
    _ = ∏ i, ∏ j, epsScale (A i j * c j) ≫ v i := Finset.prod_comm
    _ = comb v (A.mulVec c) := by
        unfold comb
        exact Finset.prod_congr rfl fun i _ => (epsScale_sum_comp (hv i) Finset.univ fun j => A i j * c j).symm

theorem isTangent_comb {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (c : Fin n → R) :
    IsTangent (comb v c) := by
  rw [isTangent_iff]
  unfold comb
  rw [comp_finProd]
  exact Finset.prod_eq_one fun i _ => (isTangent_iff _).1 (isTangent_epsScale (c i) (hv i))

theorem comb_injective {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : Function.Injective (comb v) := by
  intro c d h
  have hc : IsLieComb c v (comb v c) := (isLieComb_iff_comb c v (comb v c)).2 rfl
  have hd : IsLieComb d v (comb v c) := (isLieComb_iff_comb d v (comb v c)).2 h
  exact (hv.2 _ (isTangent_comb hv.1 c)).unique hc hd

theorem pt_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) {X : Over S'} {u u' : X ⟶ t'.G}
    (h : u.left ≫ m.φ = u'.left ≫ m.φ) : u = u' := by
  cases m with
  | mk cm cart base act lin =>
    apply Over.OverMorphism.ext
    refine cart.1.hom_ext h ?_
    rw [Over.w u, Over.w u']

end GlobalTheory.Reg.VecEig


open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent in
theorem GlobalTheory.Reg.isEigAt_iff_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (τ : E →+* ℂ) (cv : Fin M.n → R) (w : Sp (DualNumber R) ⟶ Xo.univ.t.G.left), Λ.Vec cv w → (IsEigAt c τ w ↔ M.Eig f τ cv) := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ τ cv w hw
  obtain ⟨v', u', hv', hu', rfl⟩ := hw
  obtain ⟨v, hv0, hvb, hρ⟩ := M.lie R f Λ.t' Λ.m2
  obtain rfl : v' = v := funext fun j => pt_ext Λ.m2 ((hv' j).trans (hv0 j).symm)
  have hu := (isLieComb_iff_comb _ _ _).1 hu'
  have hA := fun a j => (isLieComb_iff_comb _ _ _).1 (hρ a j)
  unfold IsEigAt MChart.Eig
  refine forall_congr' fun a => ?_
  have : IsMonHom (Λ.t'.act.act a) := Λ.t'.act.hom a
  have e1 : (u'.left ≫ Λ.m1.φ) ≫ (Xo.univ.t.act.act a).left = (u' ≫ Λ.t'.act.act a).left ≫ Λ.m1.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg (u'.left ≫ ·) (Λ.m1.act a).symm
  have e2 : spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ u'.left ≫ Λ.m1.φ =
      (epsScale (algebraMap c.F R (embK c τ a)) ≫ u').left ≫ Λ.m1.φ := by
    rw [Over.comp_left, Category.assoc]
    rfl
  rw [e1, e2, hu, comb_comp hvb.1 _ ((M.ρ a).map f) (hA a), epsScale_comb]
  constructor
  · intro h
    exact comb_injective hvb (pt_ext Λ.m1 h)
  · intro h
    rw [h]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsOpenImmersionOfSurj
section
noncomputable section

namespace GlobalTheory.Reg.ChartOpens

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem away_irreducible {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  have hi := IsFractionRing.injective O K
  refine IsLocalization.Away.mk _ (IsUnit.mk0 _ (by simpa using hϖ.ne_zero)) (fun z => ?_)
    (fun a b h => ⟨0, by rw [hi h]⟩)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) z
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  refine ⟨n, a * ↑u⁻¹, ?_⟩
  have h1 : algebraMap O K ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have h2 : algebraMap O K u * algebraMap O K ↑u⁻¹ = 1 := by rw [← map_mul]; simp
  have h3 : algebraMap O K u ≠ 0 := left_ne_zero_of_mul_eq_one h2
  rw [map_mul, map_mul, map_pow, eq_inv_of_mul_eq_one_right h2]
  field_simp

theorem exists_finset_basicOpen {A : Type} [CommRing A] [IsNoetherianRing A] (V : Set (PrimeSpectrum A))
    (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ es : Finset A, es.Nonempty ∧ (∀ e ∈ es, e ≠ 0) ∧ ∀ p, p ∈ V ↔ ∃ e ∈ es, e ∉ p.asIdeal := by
  classical
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hV.isClosed_compl
  obtain ⟨s, rfl⟩ := IsNoetherian.noetherian I
  have key : ∀ p, p ∈ V ↔ ∃ e ∈ s.filter (· ≠ 0), e ∉ p.asIdeal := by
    intro p
    have : p ∉ V ↔ (s : Set A) ⊆ p.asIdeal := by
      rw [← Set.mem_compl_iff, hI]
      exact (PrimeSpectrum.mem_zeroLocus _ _).trans Ideal.span_le
    constructor
    · intro hp
      obtain ⟨e, he, h⟩ := Set.not_subset.1 (fun h => this.2 h hp)
      exact ⟨e, Finset.mem_filter.2 ⟨he, fun h0 => h (h0 ▸ p.asIdeal.zero_mem)⟩, h⟩
    · rintro ⟨e, he, h⟩
      by_contra hp
      exact h (this.1 hp (Finset.mem_filter.1 he).1)
  obtain ⟨p, hp⟩ := hne
  obtain ⟨e, he, -⟩ := (key p).1 hp
  exact ⟨_, ⟨e, he⟩, fun e he => (Finset.mem_filter.1 he).2, key⟩

theorem isOpenImmersion_of_surj {O K A R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [CommRing A] [CommRing R] [Algebra K R] (α : O →+* A) (f : A →+* R)
    (hf : f.comp α = (algebraMap K R).comp (algebraMap O K)) (x : A) (hx : IsUnit (f x)) (hi : Function.Injective f)
    (hs : ∀ r : R, ∃ (a : A) (k : K) (N : ℕ), r * f x ^ N = algebraMap K R k * f a) :
    IsOpenImmersion (spMap f) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have := away_irreducible (K := K) hϖ
  have hfo : ∀ o, f (α o) = algebraMap K R (algebraMap O K o) := fun o => RingHom.congr_fun hf o
  letI := f.toAlgebra
  have : IsLocalization.Away (α ϖ * x) R := by
    refine IsLocalization.Away.mk _ ?_ (fun r => ?_) (fun a b h => ⟨0, by rw [hi h]⟩)
    · show IsUnit (f _)
      rw [map_mul, hfo]
      exact ((IsLocalization.Away.algebraMap_isUnit (S := K) ϖ).map _).mul hx
    · obtain ⟨a, k, N, h⟩ := hs r
      obtain ⟨n, o, ho⟩ := IsLocalization.Away.surj ϖ k
      refine ⟨N + n, α (o * ϖ ^ N) * x ^ n * a, ?_⟩
      show r * f _ ^ _ = f _
      have h2 : algebraMap K R k * f (α ϖ) ^ n = f (α o) := by
        rw [hfo, hfo, ← ho, map_mul, map_pow]
      simp only [map_mul, map_pow]
      rw [← h2]
      linear_combination (f (α ϖ) ^ (N + n) * f x ^ n) * h
  exact IsOpenImmersion.of_isLocalization (α ϖ * x)

theorem chart_opens {O K A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [CommRing A] [IsDomain A] {X Z : Scheme.{0}} (s : X ⟶ Sp O) [Flat s]
    (g : Sp A ⟶ X) [IsOpenImmersion g] (α : O →+* A) (hα : g ≫ s = spMap α) (hft : α.FiniteType)
    (t : Z ⟶ Sp K) [Smooth t] (jQ : Z ⟶ pullback s (spMap (algebraMap O K))) [IsOpenImmersion jQ]
    (hd : Dense (Set.range jQ)) (hj : jQ ≫ pullback.snd _ _ = t) :
    ∃ es : Finset A, Function.Injective α ∧ es.Nonempty ∧ (∀ e ∈ es, e ≠ 0) ∧
      (∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra K R] (f : A →+* R),
        f.comp α = (algebraMap K R).comp (algebraMap O K) → IsUnit (f e) →
          (∃ xF : Sp R ⟶ Z, xF ≫ t = spMap (algebraMap K R) ∧ xF ≫ jQ ≫ pullback.fst _ _ = spMap f ≫ g) ∧
          ∀ d : A, Function.Injective f → IsUnit (f d) →
            (∀ r : R, ∃ (a : A) (k : K) (N : ℕ), r * f (e * d) ^ N = algebraMap K R k * f a) → Algebra.Smooth K R) ∧
      ∀ (L : Type) [Field L] [Algebra K L] (f : A →+* L) (xF : Sp L ⟶ Z), xF ≫ t = spMap (algebraMap K L) →
        xF ≫ jQ ≫ pullback.fst _ _ = spMap f ≫ g →
          f.comp α = (algebraMap K L).comp (algebraMap O K) ∧ ∃ e ∈ es, f e ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have := away_irreducible (K := K) hϖ
  have hopen : IsOpenImmersion (spMap (algebraMap O K)) := IsOpenImmersion.of_isLocalization ϖ
  have hjs : (jQ ≫ pullback.fst _ _) ≫ s = t ≫ spMap (algebraMap O K) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hj]
  have hflat : α.Flat := (HasRingHomProperty.Spec_iff (P := @Flat) (φ := CommRingCat.ofHom α)).1 (by
    show Flat (spMap α)
    rw [← hα]; infer_instance)
  have hinj : Function.Injective α := by
    letI := α.toAlgebra
    have : Module.Flat O A := hflat
    exact FaithfulSMul.algebraMap_injective O A
  have hN : IsNoetherianRing A := by
    letI := α.toAlgebra
    have : Algebra.FiniteType O A := hft
    exact Algebra.FiniteType.isNoetherianRing O A
  let j := jQ ≫ pullback.fst s (spMap (algebraMap O K))
  let V : Set (PrimeSpectrum A) := g ⁻¹' Set.range j
  have hV : IsOpen V := j.isOpenEmbedding.isOpen_range.preimage g.continuous
  have hne : V.Nonempty := by
    have h0 : g (⊥ : PrimeSpectrum A) ∈ Set.range (pullback.fst s (spMap (algebraMap O K))) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
      refine Eq.trans ?_ (Scheme.Hom.comp_apply g s _)
      rw [hα]
      refine PrimeSpectrum.ext ?_
      show Ideal.comap (algebraMap O K) ⊥ = Ideal.comap α ⊥
      rw [Ideal.comap_bot_of_injective _ hinj, Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)]
    obtain ⟨y, hy⟩ := h0
    obtain ⟨_, ⟨p, hp⟩, z, rfl⟩ := hd.inter_open_nonempty
      (pullback.fst s (spMap (algebraMap O K)) ⁻¹' Set.range g)
      (g.isOpenEmbedding.isOpen_range.preimage (Scheme.Hom.continuous _)) ⟨y, _, hy.symm⟩
    exact ⟨p, z, by rw [hp]; exact Scheme.Hom.comp_apply _ _ _⟩
  obtain ⟨es, h1, h2, h3⟩ := exists_finset_basicOpen V hV hne
  refine ⟨es, hinj, h1, h2, fun e he R _ _ f hf hu => ?_, fun L _ _ f xF hx1 hx2 => ⟨?_, ?_⟩⟩
  · have hr : Set.range (spMap f ≫ g) ⊆ Set.range j := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Hom.comp_apply]
      refine (h3 (spMap f p)).2 ⟨e, he, fun h => ?_⟩
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show f e ∈ p.asIdeal from h) hu)
    let xF := IsOpenImmersion.lift j (spMap f ≫ g) hr
    have hx : xF ≫ j = spMap f ≫ g := IsOpenImmersion.lift_fac _ _ _
    have ht : xF ≫ t = spMap (algebraMap K R) := by
      rw [← cancel_mono (spMap (algebraMap O K)), Category.assoc, ← hjs, ← Category.assoc, hx, Category.assoc, hα,
        ← spMap_comp, ← spMap_comp, hf]
    refine ⟨⟨xF, ht, hx⟩, fun d hi hdu hs => ?_⟩
    have := isOpenImmersion_of_surj α f hf (e * d) (by rw [map_mul]; exact hu.mul hdu) hi hs
    have : IsOpenImmersion (xF ≫ j) := by rw [hx]; infer_instance
    have : IsOpenImmersion xF := IsOpenImmersion.of_comp xF j
    have : Smooth (spMap (algebraMap K R)) := by rw [← ht]; infer_instance
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 this)
  · have : spMap (f.comp α) = spMap ((algebraMap K L).comp (algebraMap O K)) := by
      rw [spMap_comp, spMap_comp, ← hα, ← Category.assoc, ← hx2, ← hx1, Category.assoc, hjs, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  · obtain ⟨e, he, h⟩ := (h3 (spMap f (⊥ : PrimeSpectrum L))).1
      ⟨xF (⊥ : PrimeSpectrum L), (Scheme.Hom.comp_apply xF j _).symm.trans
        ((congrArg (fun φ : Sp L ⟶ X => φ (⊥ : PrimeSpectrum L)) hx2).trans (Scheme.Hom.comp_apply _ _ _))⟩
    exact ⟨e, he, fun h0 => h (show f e ∈ (⊥ : Ideal L) from h0)⟩

theorem moduli_basicOpens :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)) (M : MChart Y), ∃ (α : O →+* Γ(Y.X, M.U)) (es : Finset Γ(Y.X, M.U)), M.hU.fromSpec ≫ Y.s = spMap α ∧ α.FiniteType ∧ Function.Injective α ∧ es.Nonempty ∧ (∀ e ∈ es, e ≠ 0) ∧ (∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R), f.comp α = (algebraMap c.F R).comp (algebraMap O c.F) → IsUnit (f e) → (∃ xF : Sp R ⟶ Xo.XF c, xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R) ∧ xF ≫ Y.j = spMap f ≫ M.hU.fromSpec) ∧ ∀ d : Γ(Y.X, M.U), Function.Injective f → IsUnit (f d) → (∀ r : R, ∃ (a : Γ(Y.X, M.U)) (k : c.F) (N : ℕ), r * f (e * d) ^ N = algebraMap c.F R k * f a) → Algebra.Smooth c.F R) ∧ ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (xF : Sp L ⟶ Xo.XF c), xF ≫ pullback.snd _ _ = spMap (algebraMap c.F L) → xF ≫ Y.j = spMap f ≫ M.hU.fromSpec → f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) ∧ ∃ e ∈ es, f e ≠ 0 := by
  intro E _ _ _ H Dw l Xo c O _ _ _ _ _ Y M
  obtain ⟨α, h1, h2, -⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c O _ Y).2.2 M.U M.hU
  have := M.dom
  have := Y.flat
  have := Y.jQ_open
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have hg : IsOpenImmersion (X := Sp Γ(Y.X, M.U)) M.hU.fromSpec := inferInstanceAs (IsOpenImmersion M.hU.fromSpec)
  obtain ⟨es, h⟩ := chart_opens (A := Γ(Y.X, M.U)) Y.s M.hU.fromSpec α h1 h2
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) Y.jQ Y.jQ_dense Y.jQ_over
  exact ⟨α, es, h1, h2, h⟩

end GlobalTheory.Reg.ChartOpens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.LawBddDataOf
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg.LawBddPf

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}

theorem nrm_add_le (Z : Comp Xo c) (G : WTZ E) (x y : AC Z) (P : Om Z →+* ℂ) :
    nrmC fn (yP Z) G (x + y) P ≤ nrmC fn (yP Z) G x P + nrmC fn (yP Z) G y P := by
  unfold nrmC
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => by positivity)
  have hc : (x + y).coeff G = x.coeff G + y.coeff G := by rfl
  rw [hc, map_add (f := _)]
  exact norm_add_le _ _

theorem nrm_smul (Z : Comp Xo c) (G : WTZ E) (a : Om Z) (x : AC Z) (P : Om Z →+* ℂ) :
    nrmC fn (yP Z) G (a • x) P = ‖P a‖ * nrmC fn (yP Z) G x P := by
  unfold nrmC
  have hc : (a • x).coeff G = a * x.coeff G := by rfl
  rw [hc, map_mul, norm_mul, mul_assoc]

theorem bdd_gen [Fintype (Comp Xo c)] (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (sg : c.F →+* ℂ) :
    BddAbove (Set.range fun p : (Σ Z : Comp Xo c, ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) sg) =>
      nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) := by
  unfold ValAtCx at hcx
  obtain ⟨B, hBd⟩ := hB sg
  refine ⟨B, ?_⟩
  rintro _ ⟨⟨Z, P⟩, rfl⟩
  have hP : (P : Om Z →+* ℂ).comp (algebraMap c.F (Om Z)) = sg := P.2
  have key : ∀ (σ : c.F →+* ℂ), σ = sg → ∀ y : FrPt Xo c (CAt σ),
      cabs (evR Xo c f y) * ∏ i, |fn σ y i|⁻¹ ^ ex Dw a n i ≤ B := by
    rintro σ rfl y
    exact hBd ⟨y, rfl⟩
  have hex : ∀ i, exZ Dw (wtZ a n) i = (ex Dw a n i : ℤ) := by
    intro i
    unfold exZ wtZ ex
    cases i <;> rfl
  have hco : (valC h a n f Z).coeff (wtZ a n) = evC h Z f := by
    unfold valC
    simp
  show nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) (P : Om Z →+* ℂ) ≤ B
  unfold nrmC
  rw [hco, hcx Z P a n f hS]
  have hs : sgOf (P : Om Z →+* ℂ) = sg := hP
  refine Eq.trans_le ?_ (key _ hs (yP Z P))
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hex i, zpow_neg, zpow_natCast, inv_pow]

theorem bdd_span (G : WTZ E) (sg : c.F →+* ℂ) (S : Set (∀ Z : Comp Xo c, AC Z))
    (hS : ∀ f ∈ S, BddAbove (Set.range fun p : (Σ Z : Comp Xo c, ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) sg) =>
      nrmC fn (yP p.1) G (f p.1) p.2)) (f : ∀ Z : Comp Xo c, AC Z)
    (hf : f ∈ (letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun Z => Algebra.toModule
      Submodule.span (𝓞 c.F) S)) :
    BddAbove (Set.range fun p : (Σ Z : Comp Xo c, ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) sg) =>
      nrmC fn (yP p.1) G (f p.1) p.2) := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    refine ⟨0, ?_⟩
    rintro _ ⟨⟨Z, P⟩, rfl⟩
    have h0 := nrm_smul (fn := fn) (yP := yP) Z G (0 : Om Z) (0 : AC Z) (P : Om Z →+* ℂ)
    rw [zero_smul, map_zero, norm_zero, zero_mul] at h0
    exact h0.le
  | add x y _ _ hx hy =>
    obtain ⟨A, hA⟩ := hx
    obtain ⟨B, hB⟩ := hy
    refine ⟨A + B, ?_⟩
    rintro _ ⟨⟨Z, P⟩, rfl⟩
    exact (nrm_add_le Z G _ _ _).trans
      (add_le_add (hA ⟨⟨Z, P⟩, rfl⟩) (hB ⟨⟨Z, P⟩, rfl⟩))
  | smul a x _ hx =>
    obtain ⟨A, hA⟩ := hx
    refine ⟨‖sg (a : c.F)‖ * A, ?_⟩
    rintro _ ⟨⟨Z, P⟩, rfl⟩
    have hP : (P : Om Z →+* ℂ).comp (algebraMap c.F (Om Z)) = sg := P.2
    have hsm : (a • x) Z = (algebraMap c.F (Om Z) (a : c.F)) • x Z := by
      rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]
      congr 1
    have hv : (P : Om Z →+* ℂ) (algebraMap c.F (Om Z) (a : c.F)) = sg (a : c.F) := by
      exact RingHom.congr_fun hP _
    show nrmC fn (yP Z) G ((a • x) Z) (P : Om Z →+* ℂ) ≤ _
    rw [hsm, nrm_smul, hv]
    exact mul_le_mul_of_nonneg_left (hA ⟨⟨Z, P⟩, rfl⟩) (norm_nonneg _)

end

theorem lawBdd_dataOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)) (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E) (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c) (nu : HeightOneSpectrum (𝓞 c.F) → ℝ) (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ) (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ), ValAtCx h yP → (∀ k, wR k ∈ sec Xo c uL.1 uL.2 ∧ SupBdd Xo c fn uL.1 uL.2 (wR k)) → (∀ k, thpR k ∈ sec Xo c uF.1 uF.2 ∧ SupBdd Xo c fn uF.1 uF.2 (thpR k)) → (etR ∈ sec Xo c uet.1 uet.2 ∧ SupBdd Xo c fn uet.1 uet.2 etR) → (ta1R ∈ sec Xo c uta1.1 uta1.2 ∧ SupBdd Xo c fn uta1.1 uta1.2 ta1R) → (ta2R ∈ sec Xo c uta2.1 uta2.2 ∧ SupBdd Xo c fn uta2.1 uta2.2 ta2R) → wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2 → wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2) → wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2 → LawBdd (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) := by
  intro E _ _ _ H Dw l Xo c _ h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hcx hw hth het hta1 hta2 e1 e2 e3
  unfold LawBdd
  set D := dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r with hD
  intro sg G F
  rintro (⟨hF, rfl⟩ | ⟨hF, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · refine bdd_span _ sg _ ?_ F hF
    rintro _ ⟨k, rfl⟩
    exact bdd_gen hcx (hw k).1 (hw k).2 sg
  · refine bdd_span _ sg _ ?_ F hF
    rintro _ ⟨k, rfl⟩
    exact bdd_gen hcx (hth k).1 (hth k).2 sg
  · have hG : D.n1 • D.wde = wtZ uet.1 uet.2 := by rw [hD]; exact e1.symm
    rw [hG]
    exact bdd_gen hcx het.1 het.2 sg
  · have hG : 2 • D.G1 = wtZ uta1.1 uta1.2 := by rw [hD]; exact e2.symm
    rw [hG]
    exact bdd_gen hcx hta1.1 hta1.2 sg
  · have hG : D.G2 = wtZ uta2.1 uta2.2 := by rw [hD]; exact e3.symm
    rw [hG]
    exact bdd_gen hcx hta2.1 hta2.2 sg

end GlobalTheory.Reg.LawBddPf
end

