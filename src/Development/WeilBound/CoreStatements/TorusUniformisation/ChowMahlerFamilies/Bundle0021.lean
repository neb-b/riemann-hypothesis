module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagRestrictLoc
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0010

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.StalkPointFactorization
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.StalkPointFactorization

theorem ext_of_affine {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {S T : CommRingCat.{0}} (i : S ⟶ T)
    (hi : Function.Injective i.hom) (f g : Spec S ⟶ X) (hf : ∀ z, f z ∈ U) (hg : ∀ z, g z ∈ U)
    (e : Spec.map i ≫ f = Spec.map i ≫ g) : f = g := by
  have hf' : Set.range f ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact hf z
  have hg' : Set.range g ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact hg z
  obtain ⟨a, ha⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec f hf')
  obtain ⟨b, hb⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec g hg')
  have ea : Spec.map a ≫ hU.fromSpec = f := by rw [ha, IsOpenImmersion.lift_fac]
  have eb : Spec.map b ≫ hU.fromSpec = g := by rw [hb, IsOpenImmersion.lift_fac]
  rw [← ea, ← eb, ← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at e
  have e2 : a ≫ i = b ≫ i := Spec.map_injective e
  have e3 : a = b := by
    ext s
    apply hi
    exact ConcreteCategory.congr_hom e2 s
  rw [← ea, ← eb, e3]

theorem fromSpecStalk_mem {X : Scheme.{0}} {U : X.Opens} {y : X} (hy : y ∈ U) (z : Spec (X.presheaf.stalk y)) :
    X.fromSpecStalk y z ∈ U := by
  have h : X.fromSpecStalk y z ∈ Set.range (X.fromSpecStalk y) := ⟨z, rfl⟩
  rw [Scheme.range_fromSpecStalk] at h
  exact Specializes.mem_open h U.isOpen hy

end PositivityTheory.Xgn.StalkPointFactorization

theorem PositivityTheory.Xgn.stalk_point_factorization : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (U : X.Opens), IsAffineOpen U → ∀ (R : Type) [CommRing R] (φ : R →+* Ω) (x : Spec (CommRingCat.of R) ⟶ X), spMap φ ≫ x = ξ → (∀ z, x z ∈ U) → ∀ (q : Cpt ξ), q.1 ∈ U → ∀ ψ : R →+* X.presheaf.stalk q.1, (genMap ξ q).comp ψ = φ → spMap ψ ≫ x = X.fromSpecStalk q.1 := by
  intro X Ω _ ξ hξ U hU R _ φ x hx hxU q hq ψ hψ
  refine PositivityTheory.Xgn.StalkPointFactorization.ext_of_affine hU (S := X.presheaf.stalk q.1) (T := CommRingCat.of Ω)
    (CommRingCat.ofHom (genMap ξ q)) (hξ.inj q) (spMap ψ ≫ x) (X.fromSpecStalk q.1) (fun z => hxU (spMap ψ z))
    (PositivityTheory.Xgn.StalkPointFactorization.fromSpecStalk_mem hq) ?_
  have h1 : spMap (genMap ξ q) ≫ spMap ψ = spMap φ := by
    rw [← hψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h2 : spMap (genMap ξ q) ≫ spMap ψ ≫ x = ξ := by
    rw [← Category.assoc, h1, hx]
  exact h2.trans (GlobalTheory.CompanionTheory.Ar.LieStalk.spMap_genMap_fromSpecStalk q).symm
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorsionGroupBaseChange
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TorsionGroupBaseChange

theorem pow_congr {S Y : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : Y ⟶ S} (h : f = f') (N : ℕ)
    (g : Over.mk f ⟶ G) (g' : Over.mk f' ⟶ G) (hg : g.left = g'.left) : g ^ N = 1 ↔ g' ^ N = 1 := by
  subst h
  have : g = g' := Over.OverMorphism.ext hg
  rw [this]

theorem mul_congr {S Y : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : Y ⟶ S} (h : f = f')
    (u v : Over.mk f ⟶ G) (u' v' : Over.mk f' ⟶ G) (hu : u.left = u'.left) (hv : v.left = v'.left) :
    (u * v).left = (u' * v').left := by
  subst h
  have h1 : u = u' := Over.OverMorphism.ext hu
  have h2 : v = v' := Over.OverMorphism.ext hv
  rw [h1, h2]

def Kill {S Y : Scheme.{0}} (G : Over S) [GrpObj G] (N : ℕ) (g : Y ⟶ G.left) : Prop :=
  (Over.homMk g rfl : Over.mk (g ≫ G.hom) ⟶ G) ^ N = 1

theorem kernel' {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T}
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}}
    (b : Y ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ G.left) (hg : g ≫ G.hom = b ≫ x) :
    Kill G N g ↔ ∃ y : Y ⟶ Γ.G.left, y ≫ Γ.G.hom = b ∧ y ≫ i = g := by
  unfold Kill
  constructor
  · intro hk
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk b
    let g₀ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk g hg
    have hk' : g₀ ^ N = 1 := (pow_congr hg.symm N g₀ (Over.homMk g rfl) rfl).2 hk
    obtain ⟨y, hy⟩ := (h.kernel Y' g₀).1 hk'
    exact ⟨y.left, Over.w y, by simpa [g₀] using hy⟩
  · rintro ⟨y, hy1, hy2⟩
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk b
    let g₀ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk g hg
    have hk' : g₀ ^ N = 1 :=
      (h.kernel Y' g₀).2 ⟨Over.homMk y hy1, by simpa [g₀] using hy2⟩
    exact (pow_congr hg.symm N g₀ (Over.homMk g rfl) rfl).1 hk'

theorem inj' {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T}
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}}
    (y z : Y ⟶ Γ.G.left) (h1 : y ≫ Γ.G.hom = z ≫ Γ.G.hom) (h2 : y ≫ i = z ≫ i) : y = z := by
  let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (z ≫ Γ.G.hom)
  have := h.inj Y' (Over.homMk y h1) (Over.homMk z rfl) (by simpa using h2)
  simpa using congrArg Over.Hom.left this

end PositivityTheory.Xgn.TorsionGroupBaseChange

open PositivityTheory.Xgn.TorsionGroupBaseChange in
theorem PositivityTheory.Xgn.torsion_group_base_change : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R'] (T : Type) [CommGroup T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S), Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x = x' → ∀ (N : ℕ) (i : Γ.G.left ⟶ G.left) (i' : Γ'.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Γ'.IsTorsionAlong G x' N i' → ∀ (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp (algebraMap R R') → (∀ t, Spec.map (CommRingCat.ofHom a) ≫ (Γ.pt t).left ≫ i = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ (algebraMap R R') F := by
  intro R R' _ _ _ _ _ T _ Γ Γ' S G _ x x' hx N i i' h h' a ha hpt
  have hKi' : Kill G N i' := (kernel' h' Γ'.G.hom i' h'.isOver).2 ⟨𝟙 _, by simp, by simp⟩
  have hi'x : i' ≫ G.hom = (Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫ x := by
    rw [Category.assoc, hx]
    exact h'.isOver
  obtain ⟨F, hF1, hF2⟩ := (kernel' h _ i' hi'x).1 hKi'
  refine ⟨F, hF2, ?_⟩
  have lift : ∀ {Z : Scheme.{0}} (u : Z ⟶ Γ.G.left) (v : Z ⟶ Spec (CommRingCat.of R')),
      u ≫ Γ.G.hom = v ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) →
      ∃ l : Z ⟶ Γ'.G.left, l ≫ F = u ∧ l ≫ Γ'.G.hom = v := by
    intro Z u v huv
    have hk : Kill G N (u ≫ i) :=
      (kernel' h (u ≫ Γ.G.hom) (u ≫ i) (by simp only [Category.assoc, h.isOver])).2 ⟨u, rfl, rfl⟩
    have hg : (u ≫ i) ≫ G.hom = v ≫ x' := by
      rw [Category.assoc, h.isOver, ← Category.assoc, huv, Category.assoc, hx]
    obtain ⟨l, hl1, hl2⟩ := (kernel' h' v (u ≫ i) hg).1 hk
    refine ⟨l, inj' h _ _ ?_ ?_, hl1⟩
    · rw [Category.assoc, hF1, ← Category.assoc, hl1, huv]
    · rw [Category.assoc, hF2, hl2]
  have uniq : ∀ {Z : Scheme.{0}} (l₁ l₂ : Z ⟶ Γ'.G.left), l₁ ≫ F = l₂ ≫ F →
      l₁ ≫ Γ'.G.hom = l₂ ≫ Γ'.G.hom → l₁ = l₂ := by
    intro Z l₁ l₂ e1 e2
    refine inj' h' _ _ e2 ?_
    rw [← hF2, ← Category.assoc, e1, Category.assoc]
  refine ⟨?_, ?_, ?_⟩
  · refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hF1
      (fun s => Classical.choose (lift s.fst s.snd s.condition))
      (fun s => (Classical.choose_spec (lift s.fst s.snd s.condition)).1)
      (fun s => (Classical.choose_spec (lift s.fst s.snd s.condition)).2)
      (fun s m h1 h2 => uniq _ _ ?_ ?_))
    · rw [h1, (Classical.choose_spec (lift s.fst s.snd s.condition)).1]
    · rw [h2, (Classical.choose_spec (lift s.fst s.snd s.condition)).2]
  · intro S' u v u₀ v₀ hu hv
    apply inj' h
    · simp only [Category.assoc, hF1, Over.w, Over.w_assoc, Over.mk_hom]
    · let U₀ : Over.mk ((Over.mk (S'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))).hom ≫ x) ⟶ G :=
        Over.homMk (u₀.left ≫ i) (by simp [h.isOver])
      let V₀ : Over.mk ((Over.mk (S'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))).hom ≫ x) ⟶ G :=
        Over.homMk (v₀.left ≫ i) (by simp [h.isOver])
      let U₁ : Over.mk (S'.hom ≫ x') ⟶ G := Over.homMk (u.left ≫ i') (by simp [h'.isOver])
      let V₁ : Over.mk (S'.hom ≫ x') ⟶ G := Over.homMk (v.left ≫ i') (by simp [h'.isOver])
      have e0 := h.mul (Over.mk (S'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))) u₀ v₀ U₀ V₀ rfl rfl
      have e1 := h'.mul S' u v U₁ V₁ rfl rfl
      have e2 : (U₀ * V₀).left = (U₁ * V₁).left :=
        mul_congr (by simp [hx]) U₀ V₀ U₁ V₁ (by simp [U₀, U₁, hu, hF2]) (by simp [V₀, V₁, hv, hF2])
      rw [← e0, e2, e1, Category.assoc, hF2]
  · refine ⟨FractionRing R, inferInstance, algebraMap R (FractionRing R), RingHom.id _, a,
      fun t => (Γ.pt t).left, fun _ _ e => e, RingHom.id_comp _, ha, fun t => ?_, fun t => ?_, fun t => ?_⟩
    · exact Over.w (Γ.pt t)
    · simp
    · apply inj' h
      · simp only [Category.assoc, Over.w, hF1, Over.w_assoc, Over.mk_hom]
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ha]
      · simp only [Category.assoc, hF2]
        exact hpt t
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XTrivflagmodAt
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_trivflagmod_at

section Lin

variable {F : Type*} [Field F] {N : ℕ}

theorem exists_basis_cols (G : Matrix (Fin N) (Fin N) F) (hG : G.det ≠ 0) :
    ∃ u : Module.Basis (Fin N) F (Fin N → F), ∀ i j, u i j = G j i := by
  classical
  have hU : IsUnit G.det := hG.isUnit
  refine ⟨(Pi.basisFun F (Fin N)).map (G.toLinearEquiv' (G.invertibleOfIsUnitDet hU)), fun i j => ?_⟩
  have : (G.toLinearEquiv' (G.invertibleOfIsUnitDet hU)) (Pi.single i 1) = G.mulVec (Pi.single i 1) := rfl
  rw [Module.Basis.map_apply, Pi.basisFun_apply, this]
  simp

theorem repr_eq (G : Matrix (Fin N) (Fin N) F) (u : Module.Basis (Fin N) F (Fin N → F))
    (hu : ∀ i j, u i j = G j i) (a v : Fin N → F) (h : G.mulVec a = v) (i : Fin N) :
    u.repr v i = a i := by
  have e : v = ∑ q, a q • u q := by
    rw [← h]
    funext j
    simp [Finset.sum_apply, hu, Matrix.mulVec, dotProduct, mul_comm]
  rw [e, u.repr_sum_self]

theorem mulVec_repr (G : Matrix (Fin N) (Fin N) F) (u : Module.Basis (Fin N) F (Fin N → F))
    (hu : ∀ i j, u i j = G j i) (v : Fin N → F) (j : Fin N) :
    v j = ∑ q, G j q * u.repr v q := by
  conv_lhs => rw [← u.sum_repr v]
  simp [Finset.sum_apply, hu, mul_comm]

theorem lat_iff {k : Type*} [CommRing k] [Algebra k F] (R : Subalgebra k F)
    (G : Matrix (Fin N) (Fin N) F) (hG : ∀ i j, G i j ∈ R) {h : F} (hh : h ∈ R)
    (hdet : G.det * h = 1) (u : Module.Basis (Fin N) F (Fin N → F))
    (hu : ∀ i j, u i j = G j i) (v : Fin N → F) :
    (∀ q, v q ∈ R) ↔ ∀ i, u.repr v i ∈ R := by
  classical
  constructor
  · intro hv i
    let G' : Matrix (Fin N) (Fin N) R := fun i j => ⟨G i j, hG i j⟩
    have hGG : G = R.val.toRingHom.mapMatrix G' := by
      ext i j
      rfl
    have hadj : ∀ i j, G.adjugate i j ∈ R := by
      intro i j
      rw [hGG, ← RingHom.map_adjugate]
      exact (G'.adjugate i j).2
    have e : G.mulVec (h • G.adjugate.mulVec v) = v := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec, smul_smul, mul_comm, hdet, one_smul]
    rw [repr_eq G u hu _ v e i]
    change h * ∑ q, G.adjugate i q * v q ∈ R
    exact mul_mem hh (sum_mem fun q _ => mul_mem (hadj i q) (hv q))
  · intro hv j
    rw [mulVec_repr G u hu v j]
    exact sum_mem fun q _ => mul_mem (hG j q) (hv q)

theorem flag_coords (G G₀ U : Matrix (Fin N) (Fin N) F) (c : F) (hc : c ≠ 0) (d : Fin N → F)
    (hd : ∀ i, d i ≠ 0) (hGU : ∀ i j, c * G i j = ∑ q, G₀ i q * U q j)
    (u w : Module.Basis (Fin N) F (Fin N → F)) (hu : ∀ i j, u i j = G j i)
    (hw : ∀ i j, w i j = (G₀ * Matrix.diagonal fun i => (d i)⁻¹) j i) (i j : Fin N) :
    w.repr (u i) j = c⁻¹ * U j i * d j := by
  refine repr_eq _ w hw (fun j => c⁻¹ * U j i * d j) _ ?_ j
  funext l
  rw [hu]
  apply mul_left_cancel₀ hc
  rw [hGU]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have := hd q
  field_simp

end Lin

section Res

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (kap redIdeal genPt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagRestrict

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra O Ω]
variable {x : (Σ k, ι k) → Ω} {Q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver (kap O) ι)} [Q.IsPrime]

theorem rs_det (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {N : ℕ} (g : Matrix (Fin N) (Fin N) Ω)
    (hg : ∀ i j, g i j ∈ locAlg x Q) :
    g.det ∈ locAlg x Q ∧ rs x Q g.det = (g.map (rs x Q)).det := by
  let ρ : locAlg x Q →+* FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver (kap O) ι ⧸ Q) :=
    { toFun := fun a => rs x Q a
      map_one' := rs_one hPQ
      map_mul' := fun a b => rs_mul hPQ a.2 b.2
      map_zero' := rs_zero hPQ
      map_add' := fun a b => rs_add hPQ a.2 b.2 }
  let g' : Matrix (Fin N) (Fin N) (locAlg x Q) := fun i j => ⟨g i j, hg i j⟩
  have h1 : g.det = ((g'.det : locAlg x Q) : Ω) := by
    have := (locAlg x Q).val.toRingHom.map_det g'
    exact this.symm
  refine ⟨h1 ▸ g'.det.2, ?_⟩
  rw [h1]
  exact ρ.map_det g'

theorem rs_unif (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {ϖ : O} (hϖ : Irreducible ϖ) {r : Ω}
    (hr : r ∈ locAlg x Q) : rs x Q (algebraMap O Ω ϖ * r) = 0 := by
  rw [rs_mul hPQ (Subalgebra.algebraMap_mem _ _) hr, rs_algebraMap hPQ,
    (IsLocalRing.residue_eq_zero_iff ϖ).2 hϖ.not_isUnit, map_zero, zero_mul]

theorem mseg_ne (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {s : ∀ k, ι k}
    (hs : mseg (genPt (kap O) Q) s ≠ 0) : mseg x s ≠ 0 := by
  rw [← aeval_segForm (R := O)]
  exact aeval_ne_zero hPQ (isMultiHomog_segForm s) (red_segForm_notMem hs)

theorem mon_ne {F : Type*} [Field F] (y : (Σ k, ι k) → F) {s : ∀ k, ι k} (hs : mseg y s ≠ 0)
    (a : K → ℤ) : chartMon y s a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hs k hk)

theorem exists_frame [DecidableEq K] (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {ϖ : O}
    (hϖ : Irreducible ϖ) {N : ℕ} {b : Fin N → K → ℤ} (H : TrivFlagMod O ϖ x N b)
    {s₀ : ∀ k, ι k} (hs₀ : mseg (genPt (kap O) Q) s₀ ≠ 0) :
    ∃ w : Module.Basis (Fin N) _ (Fin N → _),
      IsFlagFrame (genPt (kap O) Q)
        (scaledTrivBundle (kap O) (segreVec (genPt (kap O) Q)) N one_ne_zero) w b := by
  obtain ⟨g, hg, hov⟩ := H
  have hG : ∀ s, mseg (genPt (kap O) Q) s ≠ 0 →
      (∀ i j, (g s).map (rs x Q) i j ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s) ∧
      ∃ h ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s, ((g s).map (rs x Q)).det * h = 1 := by
    intro s hs
    obtain ⟨h1, h, hh, r, hr, hdet⟩ := hg s (mseg_ne hPQ hs)
    refine ⟨fun i j => (chartRing_sub hPQ hs (h1 i j)).2, rs x Q h, (chartRing_sub hPQ hs hh).2, ?_⟩
    obtain ⟨h2, h3⟩ := rs_det hPQ (g s) fun i j => (chartRing_sub hPQ hs (h1 i j)).1
    have hr' := (chartRing_sub hPQ hs hr).1
    rw [← h3, ← rs_mul hPQ h2 (chartRing_sub hPQ hs hh).1, hdet,
      rs_add hPQ (one_mem _) (mul_mem (Subalgebra.algebraMap_mem _ _) hr'), rs_one hPQ,
      rs_unif hPQ hϖ hr', add_zero]
  have hdet : ∀ s, mseg (genPt (kap O) Q) s ≠ 0 → ((g s).map (rs x Q)).det ≠ 0 := by
    intro s hs
    obtain ⟨-, h, -, hh⟩ := hG s hs
    exact left_ne_zero_of_mul_eq_one hh
  obtain ⟨w, hw⟩ := exists_basis_cols ((g s₀).map (rs x Q) *
      Matrix.diagonal fun i => (chartMon (genPt (kap O) Q) s₀ (b i))⁻¹) (by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (hdet s₀ hs₀)
      (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (mon_ne _ hs₀ _)))
  refine ⟨w, (PositivityTheory.Xgn.t_flagframe_basis (kap O) _ K ι (genPt (kap O) Q) N _
    (scaledTrivBundle (kap O) (segreVec (genPt (kap O) Q)) N one_ne_zero) w b).2 fun s hs => ?_⟩
  obtain ⟨u, hu⟩ := exists_basis_cols _ (hdet s hs)
  obtain ⟨m, U, Z, hU, hZ, hUt, hUd, -, hE⟩ := hov s s₀ (mseg_ne hPQ hs) (mseg_ne hPQ hs₀)
  obtain ⟨hc1, hc2⟩ := seg_ratio (x := x) hPQ hs₀ s
  have hc0 : (mseg (genPt (kap O) Q) s / mseg (genPt (kap O) Q) s₀) ^ m ≠ 0 :=
    pow_ne_zero _ (div_ne_zero hs hs₀)
  have hgs : ∀ i j, g s i j ∈ locAlg x Q := fun i j =>
    (chartRing_sub hPQ hs ((hg s (mseg_ne hPQ hs)).1 i j)).1
  have hg0 : ∀ i j, g s₀ i j ∈ locAlg x Q := fun i j =>
    (chartRing_sub hPQ hs₀ ((hg s₀ (mseg_ne hPQ hs₀)).1 i j)).1
  have hU' : ∀ i j, U i j ∈ locAlg x Q := fun i j => (chartRing_sub hPQ hs₀ (hU i j)).1
  have hZ' : ∀ i j, Z i j ∈ locAlg x Q := fun i j => (chartRing_sub hPQ hs₀ (hZ i j)).1
  have key := flag_coords ((g s).map (rs x Q)) ((g s₀).map (rs x Q)) (U.map (rs x Q)) _ hc0
    (fun i => chartMon (genPt (kap O) Q) s₀ (b i)) (fun i => mon_ne _ hs₀ _) (by
      intro i j
      have e : (mseg x s / mseg x s₀) ^ m * g s i j =
          ∑ q, g s₀ i q * U q j + algebraMap O Ω ϖ * Z i j := congrFun (congrFun hE i) j
      have e' := congrArg (rs x Q) e
      rw [rs_mul hPQ (pow_mem hc1 m) (hgs i j), rs_pow hPQ hc1, hc2,
        rs_add hPQ (sum_mem fun q _ => mul_mem (hg0 i q) (hU' q j))
          (mul_mem (Subalgebra.algebraMap_mem _ _) (hZ' i j)), rs_unif hPQ hϖ (hZ' i j), add_zero,
        rs_sum hPQ _ _ fun q _ => mul_mem (hg0 i q) (hU' q j)] at e'
      simp only [Matrix.map_apply]
      rw [e']
      exact Finset.sum_congr rfl fun q _ => rs_mul hPQ (hg0 i q) (hU' q j)) u w hu hw
  refine ⟨u, fun i j hij => ?_, fun i => ?_, fun v => ?_⟩
  · rw [key, Matrix.map_apply, hUt j i hij, rs_zero hPQ, mul_zero, zero_mul]
  · obtain ⟨hm1, hm2⟩ := chartMon_ratio (x := x) hPQ hs hs₀ (b i)
    rw [key, Matrix.map_apply, hUd, rs_mul hPQ (pow_mem hc1 m) hm1, rs_pow hPQ hc1, hc2, hm2,
      ← mul_assoc, inv_mul_cancel₀ hc0, one_mul, div_mul_cancel₀ _ (mon_ne _ hs₀ _)]
  · obtain ⟨h1, h, hh, hd⟩ := hG s hs
    rw [← lat_iff _ _ h1 hh hd u hu v]
    refine (mem_scaledTrivLat (R := kap O)).trans (forall_congr' fun q => ⟨?_, fun hq => ⟨v q, hq, (one_mul _).symm⟩⟩)
    rintro ⟨a, ha, e⟩
    rw [e, one_mul]
    exact ha

end Res

end PositivityTheory.Xgn.A_trivflagmod_at

open PositivityTheory.Xgn.A_trivflagmod_at GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagRestrict in
theorem PositivityTheory.Xgn.t_trivflagmod_at : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (b : Fin N → K → ℤ), TrivFlagMod O ϖ x N b → ∀ (W : Ideal (MRing ι O)), IsMultiProjPrime W → (pointIdeal O x) ≤ W → (C ϖ : MRing ι O) ∈ W → TrivFlagAt W b := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ N b H W hW hPW hϖW
  obtain ⟨hpr, -, hrel, -⟩ := SpecialIdealCorresp.proof O ϖ hϖ K ι W W hW.isPrime hϖW
  have hhom := (VocabMultiHomogIdeal.proof VocabMultiHomog.proof _ K ι _).2
    (SpecialIdealMultiHomog.proof O K ι W hW.multiHomog)
  choose s₀ hs₀ using hrel.1 hW.relevant
  have hPQ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O (mcIdeal O x) ≤ specialIdeal W :=
    Ideal.map_mono hPW
  have hs : mseg (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O)
      (specialIdeal W)) s₀ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun k _ h => hs₀ k ?_
    rw [← aeval_genPt_eq_zero_iff (specialIdeal W), aeval_X]
    exact h
  obtain ⟨w, hw⟩ := exists_frame hPQ hϖ H hs
  exact ⟨_, inferInstance, inferInstance, _, w, mcIdeal_genPt (specialIdeal W) hhom, hw⟩
end

