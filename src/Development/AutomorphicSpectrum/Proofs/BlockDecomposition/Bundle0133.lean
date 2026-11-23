module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0122
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineOpenFiniteTypeStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_open_finiteType : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] {W : X.Opens}, IsAffineOpen W → letI := (strV q W).toAlgebra; Algebra.FiniteType K Γ(X, W) := by
  first | exact @GlobalTheory.CompanionTheory.GeoFT.finiteType_affine | exact GlobalTheory.CompanionTheory.GeoFT.finiteType_affine | (intros; apply GlobalTheory.CompanionTheory.GeoFT.finiteType_affine <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicallyIndependentCoords
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoAlgInd

open MvPolynomial

def shiftE {d : ℕ} (D : ℕ) (α : Fin d →₀ ℕ) : Fin (d + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons (D - α.degree) α : Fin (d + 1) → ℕ)

theorem shiftE_zero {d : ℕ} (D : ℕ) (α : Fin d →₀ ℕ) : shiftE D α 0 = D - α.degree := rfl

theorem shiftE_succ {d : ℕ} (D : ℕ) (α : Fin d →₀ ℕ) (k : Fin d) : shiftE D α k.succ = α k := rfl

def homogP {K : Type} [Field K] {d : ℕ} (D : ℕ) (P : MvPolynomial (Fin d) K) : MvPolynomial (Fin (d + 1)) K :=
  ∑ α ∈ P.support, monomial (shiftE D α) (AddMonoidAlgebra.coeff P α)

theorem degree_le_of_mem {K : Type} [Field K] {d D : ℕ} {P : MvPolynomial (Fin d) K} (hD : P.totalDegree ≤ D)
    {α : Fin d →₀ ℕ} (hα : α ∈ P.support) : α.degree ≤ D := by
  have h := le_totalDegree hα
  rw [Finsupp.sum_fintype _ _ (by simp)] at h
  rw [Finsupp.degree_eq_sum]
  exact h.trans hD

theorem homogenize_isHomogeneous₂ {K : Type} [Field K] {d D : ℕ} {P : MvPolynomial (Fin d) K} (hD : P.totalDegree ≤ D) :
    (homogP D P).IsHomogeneous D := by
  refine IsHomogeneous.sum _ _ _ fun α hα => isHomogeneous_monomial _ ?_
  have h := degree_le_of_mem hD hα
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ, shiftE_zero]
  simp only [shiftE_succ]
  rw [← Finsupp.degree_eq_sum]
  omega

theorem aeval_homogP {K : Type} [Field K] {d D : ℕ} {P : MvPolynomial (Fin d) K} (hD : P.totalDegree ≤ D)
    {R : Type} [CommRing R] [Algebra K R] (u : R) (t : Fin d → R) :
    aeval (Fin.cons u (fun k => u * t k) : Fin (d + 1) → R) (homogP D P) = u ^ D * aeval t P := by
  conv_rhs => rw [← support_sum_monomial_coeff P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [homogP, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have h := degree_le_of_mem hD hα
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp),
    Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, shiftE_zero, shiftE_succ, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← Finsupp.degree_eq_sum]
  have e : u ^ D = u ^ (D - α.degree) * u ^ α.degree := by rw [← pow_add]; congr 1; omega
  rw [e]; ring

section Scalars

variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem map_map_apply {Y : Scheme.{0}} {A B C : Y.Opens} (f : Opposite.op C ⟶ Opposite.op B)
    (g : Opposite.op B ⟶ Opposite.op A) (s : Γ(Y, C)) :
    Y.presheaf.map g (Y.presheaf.map f s) = Y.presheaf.map (f ≫ g) s := by
  rw [Functor.map_comp, CommRingCat.comp_apply]

theorem ι_appTop_toZero (z : 𝒜 0) :
    (Proj.basicOpen 𝒜 1).ι.appTop ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) =
      (Proj.basicOpen 𝒜 1).topIso.inv
        (Proj.awayToSection 𝒜 1 (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z)) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  have h1 : (Proj.basicOpen 𝒜 1).ι ≫ (Proj 𝒜).topIso.inv ≫
      ((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv = 𝟙 _ := by
    rw [← cancel_mono (Proj.basicOpen 𝒜 1).ι]
    simp
  have h : (Proj.basicOpen 𝒜 1).ι ≫ Proj.toSpecZero 𝒜 = Proj.basicOpenToSpec 𝒜 1 ≫
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom 𝒜 _)) := by
    rw [Proj.toSpecZero, reassoc_of% h1]
  rw [h, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, Scheme.Hom.appTop, Proj.basicOpenToSpec_app_top]
  simp

theorem awayToSection_one_zero (z : 𝒜 0) :
    Proj.awayToSection 𝒜 1 (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z) =
      (Proj 𝒜).presheaf.map (homOfLE le_top).op
        ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) := by
  have h := congrArg (fun s => (Proj.basicOpen 𝒜 1).topIso.hom s) (ι_appTop_toZero 𝒜 z)
  simp only [CategoryTheory.Iso.inv_hom_id_apply] at h
  rw [← h, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  exact map_map_apply _ _ _

theorem awayToSection_zero {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) (z : 𝒜 0) :
    Proj.awayToSection 𝒜 f (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z) =
      (Proj 𝒜).presheaf.map (homOfLE le_top).op
        ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) := by
  have h := congrArg (fun φ => φ.hom (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z))
    (Proj.awayMap_awayToSection 𝒜 hf (one_mul f).symm)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    HomogeneousLocalization.awayMap_fromZeroRingHom] at h
  rw [h, awayToSection_one_zero, map_map_apply]
  rfl

end Scalars

abbrev cst {K : Type} [Field K] {N : ℕ} (g : MvPolynomial (Fin (N + 1)) K) :
    K →+* HomogeneousLocalization.Away (grK K N) g :=
  (HomogeneousLocalization.fromZeroRingHom (grK K N) _).comp (algebraMap K (grK K N 0))

theorem evV_cst {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    (q : X ⟶ Spec (CommRingCat.of K)) (hq : i ≫ PSpace.str K N = q) {g : MvPolynomial (Fin (N + 1)) K} {m : ℕ}
    (hg : g ∈ grK K N m) (V : X.Opens) (h : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (a : K) :
    evV i g V h (cst g a) = strV q V a := by
  subst hq
  simp only [evV, cst, RingHom.comp_apply]
  rw [awayToSection_zero _ hg]
  have e1 : (i ≫ PSpace.str K N).appLE ⊤ V le_top =
      (spMap (algebraMap K (grK K N 0))).appTop ≫ (Proj.toSpecZero (grK K N)).appTop ≫ i.appLE ⊤ V le_top := by
    rw [PSpace.str, ← Scheme.Hom.comp_appTop_assoc]
    exact (Scheme.Hom.appLE_comp_appLE i _ ⊤ ⊤ V (by simp) le_top).symm
  have e2 : (Proj (grK K N)).presheaf.map (homOfLE (le_top : Proj.basicOpen (grK K N) g ≤ ⊤)).op ≫
      i.appLE _ V h = i.appLE ⊤ V le_top := Scheme.Hom.map_appLE _ _ _
  have key : CommRingCat.ofHom (algebraMap K (grK K N 0)) ≫ (Scheme.ΓSpecIso _).inv ≫
      (Proj.toSpecZero (grK K N)).appTop ≫ (Proj (grK K N)).presheaf.map (homOfLE le_top).op ≫ i.appLE _ V h =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (i ≫ PSpace.str K N).appLE ⊤ V le_top := by
    rw [e2, e1, ← Category.assoc, ← Category.assoc (Scheme.ΓSpecIso _).inv, Scheme.ΓSpecIso_inv_naturality]
  exact congrArg (fun φ => φ.hom a) key

def tau {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (k : Fin d) : HomogeneousLocalization.Away (grK K N) (y 0) :=
  HomogeneousLocalization.Away.mk _ ((mem_homogeneousSubmodule e (y 0)).2 (hy 0)) 1 (y k.succ)
    (by simpa using (mem_homogeneousSubmodule e (y k.succ)).2 (hy k.succ))

def tauL {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (k : Fin d) : Localization (Submonoid.powers (y 0)) :=
  (tau y hy k).val

theorem val_cst {K : Type} [Field K] {N : ℕ} (g : MvPolynomial (Fin (N + 1)) K) (a : K) :
    (cst g a).val = algebraMap K (Localization (Submonoid.powers g)) a := by
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers g)),
    ← Localization.mk_one_eq_algebraMap]
  exact HomogeneousLocalization.val_mk _

theorem val_mul {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {f a : A} {m : ℕ} (hf : f ∈ 𝒜 m) (ha : a ∈ 𝒜 (1 • m)) :
    algebraMap A (Localization (Submonoid.powers f)) a =
      algebraMap A (Localization (Submonoid.powers f)) f * (HomogeneousLocalization.Away.mk 𝒜 hf 1 a ha).val := by
  have h : (HomogeneousLocalization.Away.mk 𝒜 hf 1 a ha).val * algebraMap A (Localization (Submonoid.powers f)) (f ^ 1) =
      algebraMap A (Localization (Submonoid.powers f)) a := by
    rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ _ _
  rw [pow_one] at h
  rw [← h, mul_comm]

theorem val_eval {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (Q : MvPolynomial (Fin d) K) :
    (eval₂Hom (cst (y 0)) (tau y hy) Q).val =
      aeval (tauL y hy) Q := by
  have h : (algebraMap (HomogeneousLocalization.Away (grK K N) (y 0)) (Localization (Submonoid.powers (y 0)))).comp
      (eval₂Hom (cst (y 0)) (tau y hy)) =
      (aeval (tauL y hy)).toRingHom := by
    refine ringHom_ext (fun a => ?_) (fun k => ?_)
    · simp only [RingHom.comp_apply, eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      exact val_cst (y 0) a
    · simp only [RingHom.comp_apply, eval₂Hom_X', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rfl
  exact RingHom.congr_fun h Q

theorem away_key {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (P : MvPolynomial (Fin d) K) {D : ℕ} (hD : P.totalDegree ≤ D)
    (hf : aeval y (homogP D P) ∈ grK K N (D • e)) :
    HomogeneousLocalization.Away.mk (grK K N) ((mem_homogeneousSubmodule e (y 0)).2 (hy 0)) D
      (aeval y (homogP D P)) hf = eval₂Hom (cst (y 0)) (tau y hy) P := by
  apply HomogeneousLocalization.val_injective
  have hc : (algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) ∘ y : Fin (d + 1) → _) =
      (Fin.cons (algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) (y 0)) (fun k => algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) (y 0) * tauL y hy k) : Fin (d + 1) → _) :=
    funext (Fin.cases rfl fun k => val_mul (grK K N) _ _)
  have h1 : algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) (aeval y (homogP D P)) =
      algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) (y 0) ^ D * aeval (tauL y hy) P := by
    rw [← aeval_homogP hD, ← hc, aeval_algebraMap_apply]
  rw [HomogeneousLocalization.Away.val_mk, val_eval, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul, h1,
    map_pow, mul_comm]

theorem algebraicIndependent_tV : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), IsIntegral X → 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → (AlgebraicIndependent K fun k => Ideal.Quotient.mk (homIdeal i) (y k)) → (V : Set X).Nonempty → letI := (strV q V).toAlgebra; AlgebraicIndependent K (tV i y hy V hV) := by
  intro K _ X N d e i y hy V hV hX he q hq hind hne
  letI := (strV q V).toAlgebra
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro P hP
  have h0 : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0) :=
    hV.trans (iInf_le (fun k => i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) 0)
  have hy0 : y 0 ∈ grK K N e := (mem_homogeneousSubmodule e (y 0)).2 (hy 0)
  have hFh : (homogP P.totalDegree P).IsHomogeneous P.totalDegree := homogenize_isHomogeneous₂ le_rfl
  have hf : aeval y (homogP P.totalDegree P) ∈ grK K N (P.totalDegree • e) := by
    rw [mem_homogeneousSubmodule, smul_eq_mul, mul_comm]
    exact hFh.aeval y hy
  have hev : evV i (y 0) V h0 (HomogeneousLocalization.Away.mk (grK K N) hy0 P.totalDegree
      (aeval y (homogP P.totalDegree P)) hf) = 0 := by
    rw [away_key y hy P le_rfl hf]
    have h : (evV i (y 0) V h0).comp (eval₂Hom (cst (y 0)) (tau y hy)) =
        (aeval (tV i y hy V hV) : MvPolynomial (Fin d) K →ₐ[K] Γ(X, V)).toRingHom := by
      refine ringHom_ext (fun a => ?_) (fun k => ?_)
      · simp only [RingHom.comp_apply, eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
        exact evV_cst i q hq hy0 V h0 a
      · simp only [RingHom.comp_apply, eval₂Hom_X', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        rfl
    exact (RingHom.congr_fun h P).trans hP
  have hmem : aeval y (homogP P.totalDegree P) ∈ homIdeal i :=
    GlobalTheory.CompanionTheory.GeoVan.mem_homIdeal_of_vanish i hX he hy0 hf V hne h0 hev
  have hz : aeval (fun k => Ideal.Quotient.mk (homIdeal i) (y k)) (homogP P.totalDegree P) = 0 := by
    have h := aeval_algebraMap_apply (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) y (homogP P.totalDegree P)
    exact h.trans (Ideal.Quotient.eq_zero_iff_mem.2 hmem)
  have hF : homogP P.totalDegree P = 0 :=
    (injective_iff_map_eq_zero _).1 ((algebraicIndependent_iff_injective_aeval).1 hind) _ hz
  have h := aeval_homogP (le_refl P.totalDegree) (1 : MvPolynomial (Fin d) K) MvPolynomial.X
  rw [hF] at h
  simpa using h.symm

end GlobalTheory.CompanionTheory.GeoAlgInd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BalancedLiftTmul
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w w'

namespace GlobalTheory.CompanionTheory.CosieveBC

section Pairing

variable (R : Type) [CommRing R] {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

def Bal {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {P : Type w'} [AddCommGroup P]
    (p : ∀ i, N i → M i → P) : Prop :=
  (∀ i n n' x, p i (n + n') x = p i n x + p i n' x) ∧ (∀ i n x x', p i n (x + x') = p i n x + p i n x') ∧
    ∀ i (r : R) n x, p i (r • n) x = p i n (r • x)

variable {R}
variable {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {P : Type w'} [AddCommGroup P]

def lift1 {p : ∀ i, N i → M i → P} (hp : Bal R p) (i : ι) : N i ⊗[R] M i →+ P :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun n => AddMonoidHom.mk' (p i n) (hp.2.1 i n))
      fun a b => AddMonoidHom.ext fun x => hp.1 i a b x)
    fun r n x => hp.2.2 i r n x

theorem balanced_lift_tmul {p : ∀ i, N i → M i → P} (hp : Bal R p) (i : ι) (n : N i) (x : M i) :
    lift1 hp i (n ⊗ₜ x) = p i n x := rfl

variable [Fintype ι] [DecidableEq ι]

def gmap {p : ∀ i, N i → M i → P} (hp : Bal R p) : (∀ i, N i ⊗[R] M i) →+ P :=
  ∑ i, (lift1 hp i).comp (Pi.evalAddMonoidHom _ i)

theorem gmap_single {p : ∀ i, N i → M i → P} (hp : Bal R p) (i : ι) (t : N i ⊗[R] M i) :
    gmap hp (Pi.single i t) = lift1 hp i t := by
  unfold gmap
  rw [AddMonoidHom.finsetSum_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

theorem hom_ext {Q : Type w'} [AddCommGroup Q] {a b : (∀ i, N i ⊗[R] M i) →+ Q}
    (h : ∀ i n x, a (Pi.single i (n ⊗ₜ x)) = b (Pi.single i (n ⊗ₜ x))) : a = b := by
  refine AddMonoidHom.functions_ext _ _ _ fun i t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul n x => exact h i n x
  | add s t hs ht => rw [Pi.single_add, map_add (f := _), map_add (f := _), hs, ht]

theorem tens_iff {p : ∀ i, N i → M i → P} (hp : Bal R p) :
    Tens R (N := N) (M := M) (M' := P) p ↔ Function.Bijective (gmap hp) := by
  constructor
  · rintro ⟨g, hg⟩
    have e : g.toAddMonoidHom = gmap hp := hom_ext fun i n x => by
      rw [gmap_single, balanced_lift_tmul]
      exact hg i n x
    rw [← e]
    exact g.bijective
  · intro h
    refine ⟨AddEquiv.ofBijective (gmap hp) h, fun i n x => ?_⟩
    change gmap hp _ = _
    rw [gmap_single, balanced_lift_tmul]

def tmap {M₂ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)] (a : ∀ i, M i →ₗ[R] M₂ i) :
    (∀ i, N i ⊗[R] M i) →+ ∀ i, N i ⊗[R] M₂ i :=
  AddMonoidHom.mk' (fun t i => (a i).lTensor (N i) (t i)) fun s t => funext fun i => map_add _ _ _

theorem tmap_single {M₂ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    (a : ∀ i, M i →ₗ[R] M₂ i) (i : ι) (n : N i) (x : M i) :
    tmap (N := N) a (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ a i x) := by
  funext k
  change (a k).lTensor (N k) ((Pi.single i (n ⊗ₜ x) : ∀ i, N i ⊗[R] M i) k) = _
  by_cases h : k = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem tmap_exact [∀ i, Module.Flat R (N i)] {M₂ M₃ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] (a : ∀ i, M i →ₗ[R] M₂ i) (b : ∀ i, M₂ i →ₗ[R] M₃ i)
    (h : ∀ i, Function.Exact (a i) (b i)) : Function.Exact (tmap (N := N) a) (tmap (N := N) b) := by
  have e := fun i => Module.Flat.lTensor_exact (N i) (h i)
  intro y
  constructor
  · intro hy
    have hy' := fun i => (e i (y i)).1 (congrFun hy i)
    choose t ht using hy'
    exact ⟨t, funext ht⟩
  · rintro ⟨t, rfl⟩
    exact funext fun i => (e i _).2 ⟨t i, rfl⟩

theorem comm_gmap {M₂ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)] {P₂ : Type w'} [AddCommGroup P₂]
    {p : ∀ i, N i → M i → P} {q : ∀ i, N i → M₂ i → P₂} (hp : Bal R p) (hq : Bal R q)
    (a : ∀ i, M i →ₗ[R] M₂ i) (b : P →+ P₂) (c : ∀ i n x, b (p i n x) = q i n (a i x)) :
    b.comp (gmap hp) = (gmap hq).comp (tmap a) := hom_ext fun i n x => by
  simp only [AddMonoidHom.comp_apply]
  rw [tmap_single, gmap_single, gmap_single, balanced_lift_tmul, balanced_lift_tmul, c]

theorem tens_five [∀ i, Module.Flat R (N i)] {M₁ M₂ M₃ M₄ M₅ : ι → Type w}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] [∀ i, AddCommGroup (M₄ i)] [∀ i, Module R (M₄ i)]
    [∀ i, AddCommGroup (M₅ i)] [∀ i, Module R (M₅ i)]
    {P₁ P₂ P₃ P₄ P₅ : Type w'} [AddCommGroup P₁] [AddCommGroup P₂] [AddCommGroup P₃] [AddCommGroup P₄] [AddCommGroup P₅]
    (a₁ : ∀ i, M₁ i →ₗ[R] M₂ i) (a₂ : ∀ i, M₂ i →ₗ[R] M₃ i) (a₃ : ∀ i, M₃ i →ₗ[R] M₄ i) (a₄ : ∀ i, M₄ i →ₗ[R] M₅ i)
    (b₁ : P₁ →+ P₂) (b₂ : P₂ →+ P₃) (b₃ : P₃ →+ P₄) (b₄ : P₄ →+ P₅)
    (ea₁ : ∀ i, Function.Exact (a₁ i) (a₂ i)) (ea₂ : ∀ i, Function.Exact (a₂ i) (a₃ i))
    (ea₃ : ∀ i, Function.Exact (a₃ i) (a₄ i))
    (eb₁ : Function.Exact b₁ b₂) (eb₂ : Function.Exact b₂ b₃) (eb₃ : Function.Exact b₃ b₄)
    {p₁ : ∀ i, N i → M₁ i → P₁} {p₂ : ∀ i, N i → M₂ i → P₂} {p₃ : ∀ i, N i → M₃ i → P₃}
    {p₄ : ∀ i, N i → M₄ i → P₄} {p₅ : ∀ i, N i → M₅ i → P₅}
    (B₁ : Bal R p₁) (B₂ : Bal R p₂) (B₃ : Bal R p₃) (B₄ : Bal R p₄) (B₅ : Bal R p₅)
    (c₁ : ∀ i n x, b₁ (p₁ i n x) = p₂ i n (a₁ i x)) (c₂ : ∀ i n x, b₂ (p₂ i n x) = p₃ i n (a₂ i x))
    (c₃ : ∀ i n x, b₃ (p₃ i n x) = p₄ i n (a₃ i x)) (c₄ : ∀ i n x, b₄ (p₄ i n x) = p₅ i n (a₄ i x))
    (t₁ : Tens R (N := N) (M := M₁) (M' := P₁) p₁) (t₂ : Tens R (N := N) (M := M₂) (M' := P₂) p₂)
    (t₄ : Tens R (N := N) (M := M₄) (M' := P₄) p₄) (t₅ : Tens R (N := N) (M := M₅) (M' := P₅) p₅) :
    Tens R (N := N) (M := M₃) (M' := P₃) p₃ := by
  rw [tens_iff B₁] at t₁
  rw [tens_iff B₂] at t₂
  rw [tens_iff B₄] at t₄
  rw [tens_iff B₅] at t₅
  rw [tens_iff B₃]
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (tmap (N := N) a₁) (tmap (N := N) a₂) (tmap (N := N) a₃) (tmap (N := N) a₄) b₁ b₂ b₃ b₄
    (gmap B₁) (gmap B₂) (gmap B₃) (gmap B₄) (gmap B₅)
    (comm_gmap B₁ B₂ a₁ b₁ c₁) (comm_gmap B₂ B₃ a₂ b₂ c₂) (comm_gmap B₃ B₄ a₃ b₃ c₃) (comm_gmap B₄ B₅ a₄ b₄ c₄)
    (tmap_exact a₁ a₂ ea₁) (tmap_exact a₂ a₃ ea₂) (tmap_exact a₃ a₄ ea₃) eb₁ eb₂ eb₃ t₁.2 t₂ t₄ t₅.1

theorem tens_of_bij {M₂ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)] {P₂ : Type w'} [AddCommGroup P₂]
    {p : ∀ i, N i → M i → P} {q : ∀ i, N i → M₂ i → P₂} (hp : Bal R p) (hq : Bal R q)
    (e : ∀ i, M₂ i ≃ₗ[R] M i) (b : P₂ ≃+ P) (c : ∀ i n x, b (q i n x) = p i n (e i x))
    (t : Tens R (N := N) (M := M) (M' := P) p) : Tens R (N := N) (M := M₂) (M' := P₂) q := by
  obtain ⟨g, hg⟩ := t
  refine ⟨(AddEquiv.piCongrRight fun i => ((e i).lTensor (N i)).toAddEquiv).trans (g.trans b.symm), fun i n x => ?_⟩
  refine b.injective ?_
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [c, ← hg]
  congr 1
  funext k
  by_cases h : k = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

end Pairing

end GlobalTheory.CompanionTheory.CosieveBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenNonemptyOfNeZeroStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basic_open_nonempty_of_ne_zero : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), IsIntegral X → ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}, 0 < e → ∀ (hg : g ∈ grK K N e), Ideal.Quotient.mk (homIdeal i) g ≠ 0 → ((i ⁻¹ᵁ Proj.basicOpen (grK K N) g : X.Opens) : Set X).Nonempty := by
  first | exact @GlobalTheory.CompanionTheory.Geo.preimage_basicOpen_nonempty_of_mk_ne_zero | exact GlobalTheory.CompanionTheory.Geo.preimage_basicOpen_nonempty_of_mk_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Geo.preimage_basicOpen_nonempty_of_mk_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveOfSurjectiveSameRank
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem bijective_of_surjective_of_VB : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (n : ℕ), VB R A n → VB R B n → ∀ f : A →ₗ[R] B,
    Function.Surjective f → Function.Bijective f := by
  intro R A B _ _ _ _ _ n hA hB f hf
  obtain ⟨fA, pA, rA⟩ := hA
  obtain ⟨fB, pB, rB⟩ := hB
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hg' : ∀ b, f (g b) = b := fun b => LinearMap.congr_fun hg b

  let s : A →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict (LinearMap.ker f) (LinearMap.id - g ∘ₗ f) (fun a => by
      simp [LinearMap.mem_ker, hg'])
  have hs : s ∘ₗ (LinearMap.ker f).subtype = LinearMap.id := by
    ext x
    have hx : f x.1 = 0 := x.2
    simp [s, hx]
  have hsurj : Function.Surjective s := fun x => ⟨x.1, LinearMap.congr_fun hs x⟩
  haveI : Module.Finite R (LinearMap.ker f) := Module.Finite.of_surjective s hsurj
  haveI : Module.Projective R (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype s hs

  let E : (LinearMap.ker f × B) ≃ₗ[R] A :=
    LinearEquiv.ofLinear ((LinearMap.ker f).subtype.coprod g) (s.prod f)
      (by
        ext a <;> simp [s, hg'])
      (by
        ext x <;> simp [s, hg'])
  have hsub : Subsingleton (LinearMap.ker f) := by
    rw [← Module.rankAtStalk_eq_zero_iff_subsingleton (R := R)]
    funext p
    have h1 := congrFun (Module.rankAtStalk_prod (R := R) (LinearMap.ker f) B) p
    have h2 := Module.rankAtStalk_eq_of_equiv (R := R) E
    have h3 := congrFun h2 p
    simp only [Pi.add_apply] at h1
    rw [h1, rA p, rB p] at h3
    simpa using h3
  refine ⟨?_, hf⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have : (⟨a, ha⟩ : LinearMap.ker f) = 0 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val this

end GlobalTheory.CompanionTheory.WedgeOf
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialValueOfFactorPullbacks
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem bv_pulln_box {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {N p q : ℕ}
    (ρ₁ : Fin (N + 1) →o Fin (p + 1)) (ρ₂ : Fin (N + 1) →o Fin (q + 1)) (x : Cn F N) :
    (bv F ρ₁ ρ₂ (pulln (boxL F) N x) = fun a _ ↦ pr F ρ₁ x a ⊗ₜ[R] 1) ∧
      (bv F ρ₁ ρ₂ (pulln (boxR F) N x) = fun _ b ↦ 1 ⊗ₜ[R] pr F ρ₂ x b) := by
  refine ⟨funext fun a => funext fun b => ?_, funext fun a => funext fun b => ?_⟩
  · show Algebra.TensorProduct.map _ _ (_ ⊗ₜ[R] 1) = _
    refine (Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_
    congr 1
    all_goals first | exact map_one _ | rfl
  · show Algebra.TensorProduct.map _ _ (1 ⊗ₜ[R] _) = _
    refine (Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_
    congr 1
    all_goals first | exact map_one _ | rfl

end GlobalTheory.CompanionTheory.HopfC
end
end

