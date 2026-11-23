module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0024
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorOfDualHom
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0047
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0046
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsCurveThroughSpecialPoint
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbedding
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

open PositivityTheory.HtPt.Mh in
theorem exists_unique_emb_btOrder_top : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), ∃! j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)), Γ.IsEmb (Γ.btOrder ⊤) j := by
  intro R _ _ T _ _ Γ
  let A := Γ.btOrder ⊤
  have htop (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤) (s : Γ(Γ.G.left, ⊤)) :
      valAt (Γ.pt t).left ⊤ h s = val (Γ.pt t).left s := by
    simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hsec (a : A) : ∃ s : Γ(Γ.G.left, ⊤), ∀ t,
      val (Γ.pt t).left s = algebraMap R (FractionRing R) (a.1 t) := by
    have ha := (PositivityTheory.HtPt.Twhopf.mem_order R T Γ ⊤ a.1).1 a.2
    obtain ⟨s, hs⟩ := (PositivityTheory.HtPt.Twhopf.reg_iff R T Γ ⊤ _).1 (ha 1)
    refine ⟨s, fun t => (htop t le_top s).symm.trans ?_⟩
    simpa only [_root_.one_mul] using hs t le_top
  have hsec_ext {s s' : Γ(Γ.G.left, ⊤)}
      (h : ∀ t, val (Γ.pt t).left s = val (Γ.pt t).left s') : s = s' := by
    rw [← sub_eq_zero]
    refine PositivityTheory.HtPt.Twhopf.sec_inj R T Γ ⊤ _ fun t ht => ?_
    rw [htop, map_sub, h, sub_self]
  have hhom_ext {B : Type} [CommRing B] {j j' : Γ.G.left ⟶ Spec (CommRingCat.of B)}
      (h : ∀ t, (Γ.pt t).left ≫ j = (Γ.pt t).left ≫ j') : j = j' :=
    pb_ext fun a => hsec_ext fun t => by rw [val_pb_comp, h, ← val_pb_comp]
  choose s hs using hsec
  let φ : A →+* Γ(Γ.G.left, ⊤) :=
    { toFun := s
      map_one' := hsec_ext fun t => by rw [hs, map_one]; simp
      map_mul' := fun a b => hsec_ext fun t => by rw [hs, map_mul, hs, hs]; simp
      map_zero' := hsec_ext fun t => by rw [hs, map_zero]; simp
      map_add' := fun a b => hsec_ext fun t => by rw [hs, map_add (f := _), hs, hs]; simp }
  obtain ⟨j, hj⟩ := exists_pb φ
  have hpt : ∀ t, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom
      ((algebraMap R (FractionRing R)).comp
        ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom))) := by
    intro t
    apply comp_eq_spec
    intro a
    rw [hj]
    exact hs a t
  refine ⟨j, ⟨?_, hpt⟩, fun j' hj' => hhom_ext fun t => by rw [hj'.pt, hpt]⟩
  apply hhom_ext
  intro t
  rw [← Category.assoc, hpt, spec_comp, Over.w (Γ.pt t)]
  show _ = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  congr 2

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeSpanIndependent
section
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem HodgeLat.quot_det_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (u : Fin r → V × Module.Dual Ω V), (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → (𝓗.quot σ).IsVB r (HT.eigSp 𝓗.ρH σ) ∧ (detLat (𝓗.quot σ) u).IsVB 1 ⊤ ∧ ∀ (p : Cpt ξ) (A : Matrix (Fin r) (Fin r) Ω), (𝓗.quot σ).IsFrameAt (fun i => ∑ j, A i j • u j) p → (detLat (𝓗.quot σ) u).IsGenAt p A.det := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar r 𝓗 σ u hσ hu hspan
  have hvb : (𝓗.quot σ).IsVB r (HT.eigSp 𝓗.ρH σ) := by
    intro p _
    obtain ⟨U, hpU, x, hx⟩ := 𝓗.free p
    refine ⟨U, hpU, fun i => HT.eigProj 𝓗.ρH σ (x i), HodgeDeterminantLattice.span_eigProj σ (hx p hpU), ?_⟩
    intro q _ hq
    refine ⟨HodgeDeterminantLattice.linearIndependent_eigProj σ (hx q hq), ?_⟩
    rw [HodgeLat.quot_apply]
    exact HodgeDeterminantLattice.eigQuot_eq_span σ (hx q hq) (fun a => ⟨⟨σ a, hσ q a⟩, rfl⟩)
  exact ⟨hvb, HodgeDeterminantLattice.detLat_isVB hvb hu hspan, fun p A hA => HodgeDeterminantLattice.detLat_of_frame hu hA⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieChartOfSmoothChart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartDer

open scoped TensorProduct

theorem exists_diffModule {A B : Type} [CommRing A] [CommRing B] (g : B →+* A) (hg : g.Smooth)
    {R : Type} [CommRing R] (f : R) (u : A →+* Localization.Away f) :
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module (Localization.Away f) P)
      (_ : IsScalarTower R (Localization.Away f) P) (_ : Module.Finite (Localization.Away f) P)
      (_ : Module.Projective (Localization.Away f) P) (d : A → P),
      (∀ a b, d (a + b) = d a + d b) ∧ (∀ a b, d (a * b) = u a • d b + u b • d a) ∧ (∀ b, d (g b) = 0) ∧
      ∀ (C : Type) [CommRing C] [Algebra R C] (κ : Localization.Away f →+* C),
        κ.comp (algebraMap R (Localization.Away f)) = algebraMap R C →
        (∀ (w : P →ₗ[R] C) (r : Localization.Away f) (p : P), w (r • p) = κ r * w p) ∧
        (∀ w w' : P →ₗ[R] C, (∀ a, w (d a) = w' (d a)) → w = w') ∧
        (∀ δ : A → C, (∀ a b, δ (a + b) = δ a + δ b) →
          (∀ a b, δ (a * b) = κ (u a) * δ b + κ (u b) * δ a) → (∀ b, δ (g b) = 0) →
          ∃ w : P →ₗ[R] C, ∀ a, w (d a) = δ a) := by
  letI iB : Algebra B A := g.toAlgebra
  haveI : Algebra.Smooth B A := hg
  letI iA : Algebra A (Localization.Away f) := u.toAlgebra
  haveI tw : IsScalarTower R (Localization.Away f) (Localization.Away f ⊗[A] Ω[A⁄B]) := inferInstance
  have hsmul : ∀ (a : A) (x : Ω[A⁄B]), (1 : Localization.Away f) ⊗ₜ[A] (a • x) =
      u a • ((1 : Localization.Away f) ⊗ₜ[A] x) := fun a x => by
    have e : a • (1 : Localization.Away f) = u a := by
      rw [Algebra.smul_def, _root_.mul_one]; rfl
    rw [← TensorProduct.smul_tmul, e, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  refine ⟨Localization.Away f ⊗[A] Ω[A⁄B], inferInstance, inferInstance, inferInstance, tw,
    Module.Finite.base_change A _ _, inferInstance, fun a => 1 ⊗ₜ[A] KaehlerDifferential.D B A a,
    fun a b => by simp [TensorProduct.tmul_add], fun a b => ?_, fun b => ?_, ?_⟩
  · simp only [Derivation.leibniz, TensorProduct.tmul_add, hsmul]
  · have : g b = algebraMap B A b := rfl
    simp [this]
  intro C _ _ κ hκ
  letI aC : Algebra (Localization.Away f) C := κ.toAlgebra
  haveI : IsScalarTower R (Localization.Away f) C := IsScalarTower.of_algebraMap_eq' hκ.symm
  have lin : ∀ (w : (Localization.Away f ⊗[A] Ω[A⁄B]) →ₗ[R] C) (r : Localization.Away f) p,
      w (r • p) = κ r * w p := fun w r p => by
    have h : w (r • p) = r • w p :=
      (w.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)).map_smul r p
    rw [h, Algebra.smul_def]
    rfl
  refine ⟨lin, fun w w' h => LinearMap.ext fun p => ?_, fun δ h1 h2 h3 => ?_⟩
  · have hD : ∀ x : Ω[A⁄B], w ((1 : Localization.Away f) ⊗ₜ[A] x) = w' ((1 : Localization.Away f) ⊗ₜ[A] x) := by
      intro x
      have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D B A)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hx, hy]
      | smul a x _ ih => rw [hsmul, lin, lin, ih]
    induction p using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add (f := _), hx, hy]
    | tmul r x =>
      have e : r ⊗ₜ[A] x = r • ((1 : Localization.Away f) ⊗ₜ[A] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e, lin, lin, hD]
  · letI aA : Algebra A C := (κ.comp u).toAlgebra
    haveI : IsScalarTower A (Localization.Away f) C := IsScalarTower.of_algebraMap_eq' rfl
    letI aB : Algebra B C := ((κ.comp u).comp g).toAlgebra
    haveI : IsScalarTower B A C := IsScalarTower.of_algebraMap_eq' rfl
    let L : A →ₗ[B] C :=
      { toFun := δ
        map_add' := h1
        map_smul' := fun b a => by
          change δ (g b * a) = κ (u (g b)) * δ a
          rw [h2, h3, mul_zero, add_zero] }
    let Dv : Derivation B A C := Derivation.mk' L fun a b => by
      change δ (a * b) = κ (u a) * δ b + κ (u b) * δ a
      exact h2 a b
    refine ⟨(Dv.liftKaehlerDifferential.liftBaseChange (Localization.Away f)).restrictScalars R, fun a => ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearMap.liftBaseChange_tmul, one_smul,
      Derivation.liftKaehlerDifferential_comp_D]
    rfl

def dualOf {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C)
    (h1 : ∀ a b, δ (a + b) = δ a + δ b) (h2 : ∀ a b, δ (a * b) = v a * δ b + v b * δ a) :
    A →+* DualNumber C where
  toFun a := TrivSqZeroExt.inl (v a) + TrivSqZeroExt.inr (δ a)
  map_one' := by
    have h : δ 1 = 0 := by simpa using h2 1 1
    ext <;> simp [h]
  map_mul' a b := by
    ext
    · simp
    · simp [h2, TrivSqZeroExt.snd_mul]
      ring
  map_zero' := by
    have h : δ 0 = 0 := by simpa using h1 0 0
    ext <;> simp [h]
  map_add' a b := by
    ext
    · simp
    · simp [h1]

theorem dualOf_fst {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C) (h1 h2) (a : A) :
    (dualOf v δ h1 h2 a).fst = v a := by
  simp [dualOf]

theorem dualOf_snd {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C) (h1 h2) (a : A) :
    (dualOf v δ h1 h2 a).snd = δ a := by
  simp [dualOf]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem one_left {T : Scheme.{0}} {X M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem exists_lieModel {S : Scheme.{0}} (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (v : Γ(G.left, U) →+* C)
    (h1 : (1 : Over.mk y ⟶ G).left = spMap v ≫ hU.fromSpec)
    {E : Type} [AddCommGroup E] [Module C E] (δ : E → Γ(G.left, U) → C)
    (hadd : ∀ e a b, δ e (a + b) = δ e a + δ e b)
    (hmul : ∀ e a b, δ e (a * b) = v a * δ e b + v b * δ e a)
    (hker : ∀ e b, δ e ((G.hom.appLE V U hUV).hom b) = 0)
    (hEadd : ∀ e e' a, δ (e + e') a = δ e a + δ e' a)
    (hEsmul : ∀ (c : C) e a, δ (c • e) a = c * δ e a)
    (hinj : ∀ e e', (∀ a, δ e a = δ e' a) → e = e')
    (hsurj : ∀ δ' : Γ(G.left, U) → C, (∀ a b, δ' (a + b) = δ' a + δ' b) →
      (∀ a b, δ' (a * b) = v a * δ' b + v b * δ' a) →
      (∀ b, δ' ((G.hom.appLE V U hUV).hom b) = 0) → ∃ e, ∀ a, δ e a = δ' a) :
    ∃ M : LieModel G y E, ∀ e, ∃ φ : Γ(G.left, U) →+* DualNumber C,
      (∀ a, (φ a).fst = v a) ∧ (∀ a, (φ a).snd = δ e a) ∧ (M.pt e).left = spMap φ ≫ hU.fromSpec := by
  obtain ⟨c1, c2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.TanChart.tan_iff_der S G U V hU hV hUV C y v h1
  let φ : E → (Γ(G.left, U) →+* DualNumber C) := fun e => dualOf v (δ e) (hadd e) (hmul e)
  have φfst : ∀ e a, (φ e a).fst = v a := fun e a => dualOf_fst ..
  have φsnd : ∀ e a, (φ e a).snd = δ e a := fun e a => dualOf_snd ..
  have ex : ∀ e, ∃ t : epsAt y ⟶ G, IsTanAt G y t ∧ t.left = spMap (φ e) ≫ hU.fromSpec :=
    fun e => c1 (φ e) (φfst e) fun b => by rw [φsnd, hker]
  choose pt ptan pleft using ex
  have spinj : ∀ ψ ψ' : Γ(G.left, U) →+* DualNumber C,
      spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec → ψ = ψ' := fun ψ ψ' h => by
    have h2 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h)
    simpa using congrArg CommRingCat.Hom.hom h2
  refine ⟨{ pt := pt, tan := ptan, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun e => ⟨φ e, φfst e, φsnd e, pleft e⟩⟩
  · intro e e' h
    have h2 := spinj _ _ (by rw [← pleft, ← pleft, h] : spMap (φ e) ≫ hU.fromSpec = spMap (φ e') ≫ hU.fromSpec)
    exact hinj _ _ fun a => by rw [← φsnd, h2, φsnd]
  · intro t ht
    obtain ⟨ψ, f1, f2, f3⟩ := c2 t ht
    obtain ⟨e, he⟩ := hsurj (fun a => (ψ a).snd) (fun a b => by simp)
      (fun a b => by
        simp only [map_mul, TrivSqZeroExt.snd_mul, f1]
        simp [mul_comm, add_comm]) f2
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    have h2 : φ e = ψ := RingHom.ext fun a => TrivSqZeroExt.ext (by rw [φfst, f1]) (by rw [φsnd, he])
    rw [pleft, f3, h2]
  · intro e e'
    refine Over.OverMorphism.ext ?_
    rw [_root_.GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq S G U hU C y v h1 (pt e) (pt e') (ptan e) (ptan e') (φ e) (φ e') (φ (e + e'))
      (φfst e) (φfst e') (φfst _) (fun a => by rw [φsnd, φsnd, φsnd, hEadd]) (pleft e) (pleft e'), pleft]
  · intro c e
    have h2 : φ (c • e) = (epsMul c).comp (φ e) := RingHom.ext fun a => TrivSqZeroExt.ext
      (by simp [epsMul, φfst]) (by simp [epsMul, φsnd, hEsmul])
    rw [pleft, pleft, h2, spMap_comp, Category.assoc]

theorem lieChart_of_smooth_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Sp R ⟶ S) (f : R) (U : G.left.Opens) (V : S.Opens)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V), RingHom.Smooth (G.hom.appLE V U hUV).hom →
  ∀ u : Γ(G.left, U) →+* Localization.Away f,
    (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec → LieChart G x f := by
  intro S G _ R _ x f U V hU hV hUV hsm u h1
  obtain ⟨P, i1, i2, i3, i4, i5, i6, d, dadd, dmul, dker, hP⟩ :=
    exists_diffModule (G.hom.appLE V U hUV).hom hsm f u
  have hunit : ∀ (C : Type) [CommRing C] [Algebra R C] (κ : Localization.Away f →+* C),
      κ.comp (algebraMap R (Localization.Away f)) = algebraMap R C →
      (1 : Over.mk (spMap (algebraMap R C) ≫ x) ⟶ G).left = spMap (κ.comp u) ≫ hU.fromSpec := by
    intro C _ _ κ hκ
    rw [one_left] at h1 ⊢
    simp only [Over.mk_hom] at h1 ⊢
    have e : spMap (algebraMap R C) = spMap κ ≫ spMap (algebraMap R (Localization.Away f)) := by
      rw [← spMap_comp, hκ]
    have h3 : ((spMap κ ≫ spMap (algebraMap R (Localization.Away f))) ≫ x) ≫ η[G].left =
        spMap κ ≫ (spMap (algebraMap R (Localization.Away f)) ≫ x) ≫ η[G].left := by
      simp only [Category.assoc]
    rw [e, h3, h1, spMap_comp κ u]
    exact (Category.assoc _ _ _).symm
  have key : ∀ (C : Type) [CommRing C] [Algebra R C] (hC : IsUnit (algebraMap R C f)),
      ∃ M : LieModel G (spMap (algebraMap R C) ≫ x) (P →ₗ[R] C), ∀ w,
        ∃ φ : Γ(G.left, U) →+* DualNumber C,
          (∀ a, (φ a).fst = ((IsLocalization.Away.lift f hC).comp u) a) ∧ (∀ a, (φ a).snd = w (d a)) ∧
          (M.pt w).left = spMap φ ≫ hU.fromSpec := by
    intro C _ _ hC
    have hκ := IsLocalization.Away.lift_comp (S := Localization.Away f) f hC
    obtain ⟨l1, l2, l3⟩ := hP C _ hκ
    exact exists_lieModel (E := P →ₗ[R] C) G U V hU hV hUV C _ _ (hunit C _ hκ)
      (fun (w : P →ₗ[R] C) a => w (d a))
      (fun w a b => by simp [dadd]) (fun w a b => by simp only [dmul, map_add (f := _), l1, RingHom.comp_apply])
      (fun w b => by simp [dker]) (fun w w' a => rfl) (fun c w a => by simp) l2 l3
  refine ⟨P, i1, i2, i3, i4, i5, i6, fun C _ _ hC => (key C hC).choose, ?_⟩
  intro C C' _ _ _ _ hC hC' c w
  obtain ⟨φ, f1, f2, f3⟩ := (key C hC).choose_spec w
  obtain ⟨φ', g1, g2, g3⟩ := (key C' hC').choose_spec (c.toLinearMap ∘ₗ w)
  have hc : c.toRingHom.comp (IsLocalization.Away.lift (S := Localization.Away f) f hC) =
      IsLocalization.Away.lift (S := Localization.Away f) f hC' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
    rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]
    exact c.comp_algebraMap
  have h2 : φ' = (dualMap c.toRingHom).comp φ := RingHom.ext fun a => TrivSqZeroExt.ext
    (by
      simp only [g1, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, f1]
      exact (RingHom.congr_fun hc (u a)).symm)
    (by
      simp only [g2, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, f2]
      rfl)
  rw [g3, f3, h2, spMap_comp, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.ChartDer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleNormalProperPullback
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lat_isGenAt_of_proper_birational : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') [IsProper f], Dominates ξ' ξ f i → Function.Bijective i → IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p' : Cpt ξ', f p'.1 ⤳ p.1 → (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t)) → L.IsGenAt p t :=
  @PositivityTheory.Xgn.line_lattice_proper_pushdown

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineLatticeGenericSections
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_regAt_genPt_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (a : Ω) :
    a ∈ regAt ξ ⟨genPt ξ, specializes_refl _⟩ := by
  obtain ⟨g, hg⟩ := h.bij.2 a
  refine ⟨g, ?_⟩
  rw [← hg]
  simp only [genMap, genPt, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  rfl

theorem genPt_mem_genFibre_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (O : Type) [CommRing O] [Algebra O Ω]
    (hi : Function.Injective (algebraMap O Ω)) :
    (⟨genPt ξ, specializes_refl _⟩ : Cpt ξ) ∈ genFibre O ξ := fun o ho =>
  ⟨fun h0 => ho (hi (by rw [h0, map_zero])), mem_regAt_genPt_of_isCptGen h _,
    mem_regAt_genPt_of_isCptGen h _⟩

theorem mem_lat_genFibre_iff_const_mul : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ConstClosed O Ω → ∀ (L : Lat ξ Ω) (t : Ω), (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∀ u : Ω, (∀ p ∈ genFibre O ξ, u ∈ L p) ↔ ∃ x y : O, y ≠ 0 ∧ u * algebraMap O Ω y = algebraMap O Ω x * t := by
  intro X Ω _ ξ O _ _ _ s _ hs hi hξ hc L t ht u
  have ht0 : t ≠ 0 := (ht _ (genPt_mem_genFibre_of_isCptGen hξ O hi)).1
  constructor
  · intro hu
    have hreg : ∀ p ∈ genFibre O ξ, u / t ∈ regAt ξ p := by
      intro p hp
      have h1 := hu p hp
      rw [(ht p hp).2] at h1
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
      replace hc : (c : Ω) * t = u := hc
      rw [← hc, mul_div_cancel_right₀ _ ht0]
      exact c.2
    obtain ⟨x, y, hy, e⟩ := hc _ ((_root_.GlobalTheory.CompanionTheory.Ar.Flat.isIntegral_and_isAlgebraic_of_regular X Ω ξ O s hs hi hξ (u / t)).2 hreg)
    refine ⟨x, y, hy, ?_⟩
    rw [← e]
    field_simp
  · rintro ⟨x, y, hy, e⟩ p hp
    rw [(ht p hp).2]
    have hx : algebraMap O Ω x ∈ regAt ξ p := by
      by_cases h0 : x = 0
      · rw [h0, map_zero]; exact zero_mem _
      · exact (hp x h0).2.1
    have hyu := hp y hy
    refine Submodule.mem_span_singleton.2 ⟨⟨_, mul_mem hx hyu.2.2⟩, ?_⟩
    change algebraMap O Ω x * (algebraMap O Ω y)⁻¹ * t = u
    have := hyu.1
    rw [mul_right_comm, ← e]
    field_simp

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuDecompositionOfMinorsStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lu_decomposition_of_minors : ∀ {F : Type} [Field F] {r : ℕ} (Y : Matrix (Fin r) (Fin r) F), (∀ (k : ℕ) (hk : k ≤ r), kMinor Y k hk (Fin.castLE hk) ≠ 0) → ∃ C V : Matrix (Fin r) (Fin r) F, (∀ l k, k < l → C l k = 0) ∧ (∀ l k, l < k → V l k = 0) ∧ (∀ l, V l l = 1) ∧ Y * C = V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalizedMinorExtendsStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_minor_extends : ∀ {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F) (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin n) (I : Fin k → Fin n), NormAt O Y (k + 1) hk I' → NormAt O Y k (Nat.le_of_succ_le hk) I → ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧ NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.normAt_exchange | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.normAt_exchange | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.normAt_exchange <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecialFibreClosedSpecialization
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_fibreCurve_through_closed_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ∀ (y x : Cpt ξ) (g : Ω), ¬ unitAt ξ y (algebraMap O Ω ϖ) → y.1 ⤳ x.1 → IsClosed ({x.1} : Set X) → g ∈ regAt ξ x → unitAt ξ y g → ¬ unitAt ξ x g → ∃ (Γ : FibreCurve ξ (algebraMap O Ω ϖ)) (i : Γ.C.I), y.1 ⤳ centre Γ.η ∧ unitAt ξ ⟨centre Γ.η, Γ.η_spec⟩ g ∧ centre (Γ.z i) = x.1 := by
  exact @PositivityTheory.Xgn.exists_curve_through_special_point

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistIsoNonempty
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem tw_iso_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H), Nonempty (TwIso D g) :=
  PositivityTheory.UnitarySelfGeneration.tw_iso

end GlobalTheory.CompanionTheory.Ar
end

