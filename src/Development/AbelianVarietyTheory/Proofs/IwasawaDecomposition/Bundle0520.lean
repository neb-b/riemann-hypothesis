module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueRuleOfRegular

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesFlagsIffAdaptedFrameAtImage
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.CarriesAt

section Tri

variable {ι : Type} {m : ι → ℕ} {K : Type} [Field K]

theorem par_of_tri {h : Mat m K} (hd : ∀ τ i, h τ i i ≠ 0) (hl : ∀ τ i k, i < k → h τ i k = 0) : Par m ⊤ h := fun τ => by
  have hdet : (h τ).det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular (h τ) fun i j hij => hl τ i j hij]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hd τ i
  exact ⟨fun _ _ => trivial, hdet, trivial, fun i j _ hij => hl τ i j hij⟩

theorem Par.diag_ne {O : Subring K} {h : Mat m K} (hp : Par m O h) (τ : ι) (i : Fin (m τ)) : h τ i i ≠ 0 := by
  have := hp.det_ne τ
  rw [Matrix.det_of_lowerTriangular (h τ) fun a b hab => (hp τ).2.2.2 a b a.2 hab] at this
  exact Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ i)

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_cast {R : Type} [CommRing R] {φ : c.F →+* R} {x x' : Sp R ⟶ Z.X} (h : x = x') (g : EigFrame Z φ x) :
    ∃ g' : EigFrame Z φ x', ∀ τ i, g'.v τ i = g.v τ i := by
  subst h
  exact ⟨g, fun _ _ => rfl⟩

theorem spMap_dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (ρ : R →+* R') (ψ : R' →+* R'') :
    spMap (dualMap (ψ.comp ρ)) = spMap (dualMap ψ) ≫ spMap (dualMap ρ) := by
  have e : dualMap (ψ.comp ρ) = (dualMap ψ).comp (dualMap ρ) := by
    ext r <;> simp [dualMap]
  rw [e]
  simp [spMap, Spec.map_comp]

theorem coord_of_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x}
    {f' : EigFrame Z φ' x'} {g : EigFrame Z φ'' x''} {ρ : R →+* R'} {ψ : R' →+* R''} {A : Mat Dw.mult R''}
    (hx : x' = spMap ρ ≫ x) (hφ : φ' = ρ.comp φ) (hv : ∀ τ i, f'.v τ i = spMap (dualMap ρ) ≫ f.v τ i)
    (h : f.Coord (ψ.comp ρ) g A) : f'.Coord ψ g A := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun τ i => ?_⟩
  · rw [h1, hx, ← Category.assoc]
    congr 1
    simp [spMap, Spec.map_comp]
  · rw [h2, hφ, RingHom.comp_assoc]
  · have e : (fun k => spMap (dualMap ψ) ≫ f'.v τ k) = fun k => spMap (dualMap (ψ.comp ρ)) ≫ f.v τ k := by
      funext k
      rw [hv, spMap_dualMap_comp, Category.assoc]
    rw [e]
    exact h3 τ i

theorem algebraMap_eq_comp_specializes {X : Scheme.{0}} [IsIntegral X] {y y' : X} (h : y' ⤳ y) :
    algebraMap (X.presheaf.stalk y) X.functionField =
      (algebraMap (X.presheaf.stalk y') X.functionField).comp (X.presheaf.stalkSpecializes h).hom :=
  (congrArg CommRingCat.Hom.hom
    (TopCat.Presheaf.stalkSpecializes_comp X.presheaf (genericPoint_specializes y') h)).symm

theorem exists_adapted {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {S : Fr (ratOf C.Y) Dw.mult Dw.mult}
    {A₀ : Mat Dw.mult C.Y.Fn} (hA₀ : A₀ ∈ S.S (genericPoint C.Y.X))
    (hTied : ∀ y : C.Y.X, ∀ A ∈ S.S y, ∃ (φ : c.F →+* C.Y.X.presheaf.stalk y)
      (f : EigFrame Z φ (stalkPt C.Y y ≫ C.π ≫ genι Z)),
      f.Coord (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 (A₀ * A⁻¹))
    {K : Type} [Field K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} (g : EigFrame Z φ x) {y y' : C.Y.X} (hsp : y' ⤳ y)
    (ψ' : C.Y.X.presheaf.stalk y' →+* K) {φ₁ : c.F →+* C.Y.X.presheaf.stalk y}
    (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) {T : Mat Dw.mult C.Y.Fn} {h : Mat Dw.mult K}
    (hT1 : f.Coord (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 T)
    (hT : Par Dw.mult ⊤ T)
    (hh1 : f.Coord (ψ'.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) g h) :
    ∃ A ∈ S.S y', ∃ (φ₂ : c.F →+* C.Y.X.presheaf.stalk y') (f₁ : EigFrame Z φ₂ (stalkPt C.Y y' ≫ C.π ≫ genι Z)),
      f₁.Coord (algebraMap (C.Y.X.presheaf.stalk y') C.Y.X.functionField) C.f0 (A₀ * A⁻¹) ∧ f₁.Coord ψ' g h := by
  set ρ := (C.Y.X.presheaf.stalkSpecializes hsp).hom with hρdef
  set alg := algebraMap (C.Y.X.presheaf.stalk y') C.Y.X.functionField with halg
  have hρ : spMap ρ ≫ stalkPt C.Y y = stalkPt C.Y y' := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hinj : Function.Injective alg := IsFractionRing.injective _ _

  have hfS : f.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f inferInstance
  obtain ⟨f₀, hf₀⟩ := hfS (C.Y.X.presheaf.stalk y') ρ
  have hx' : spMap ρ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z = stalkPt C.Y y' ≫ C.π ≫ genι Z := by
    rw [← Category.assoc, hρ]
  obtain ⟨f', hf'⟩ := exists_cast hx' f₀
  have hv : ∀ τ i, f'.v τ i = spMap (dualMap ρ) ≫ f.v τ i := fun τ i => (hf' τ i).trans (hf₀ τ i)
  have hT1' : f'.Coord alg C.f0 T :=
    coord_of_bc hx'.symm rfl hv (algebraMap_eq_comp_specializes hsp ▸ hT1)
  have hh1' : f'.Coord ψ' g h := coord_of_bc hx'.symm rfl hv hh1

  obtain ⟨A', hA'⟩ := S.nonempty y'
  obtain ⟨φ'', f'', hf''⟩ := hTied y' A' hA'
  obtain rfl : φ'' = ρ.comp φ₁ := RingHom.ext fun a => hinj (by
    have e1 := RingHom.congr_fun hf''.2.1 a
    have e2 := RingHom.congr_fun hT1'.2.1 a
    exact e1.symm.trans e2)
  have hS'' : f''.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f'' inferInstance
  have hid : stalkPt C.Y y' ≫ C.π ≫ genι Z = spMap (RingHom.id _) ≫ stalkPt C.Y y' ≫ C.π ≫ genι Z := by
    rw [show spMap (RingHom.id (C.Y.X.presheaf.stalk y')) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  obtain ⟨⟨G, hG, -⟩, hGu⟩ := (GlobalTheory.ShFam.EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ f'' _ (ρ.comp φ₁) _ (RingHom.id _) inferInstance hS''
    hid (RingHom.id_comp _).symm).1 f'
  have hGd := hGu G hG
  have hcomp : f''.Coord alg C.f0 (T * G.map alg) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ f'' _ _ _ f' _ _ _ C.f0 (RingHom.id _) alg G T inferInstance hG hT1'
    rwa [RingHom.comp_id] at this
  have heq : A₀ * A'⁻¹ = T * G.map alg :=
    (((GlobalTheory.ShFam.EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ f'' _ _ _ alg inferInstance hS'' hf''.1 hf''.2.1).1 C.f0).1).unique hf'' hcomp
  have hAA : T⁻¹ * A₀ * A'⁻¹ = G.map alg := by
    rw [mul_assoc, heq, ← mul_assoc, Mat.inv_mul hT.det_ne, one_mul]
  have hPg : Par Dw.mult ((ratOf C.Y).O (genericPoint C.Y.X)).toSubring (A₀ * A'⁻¹) :=
    (Fr.mem_iff (Fr.mem_genericPoint hA')).1 hA₀
  have hlow : Par Dw.mult ⊤ (G.map alg) := by
    rw [← hAA, mul_assoc]
    exact hT.inv.mul (hPg.mono le_rfl le_top)
  have hpar : Par Dw.mult ((ratOf C.Y).O y').toSubring (T⁻¹ * A₀ * A'⁻¹) := fun τ => by
    rw [hAA]
    have hdet : (G.map alg τ).det = alg (G τ).det := (alg.map_det (G τ)).symm
    obtain ⟨u, hu⟩ := hGd τ
    refine ⟨fun i j => mem_O_ratOf.2 ⟨G τ i j, rfl⟩, hlow.det_ne τ, ?_, fun i j hi hij => (hlow τ).2.2.2 i j hi hij⟩
    refine mem_O_ratOf.2 ⟨(u⁻¹ : (C.Y.X.presheaf.stalk y')ˣ), ?_⟩
    rw [hdet, ← hu]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨T⁻¹ * A₀, (Fr.mem_iff hA').2 hpar, ρ.comp φ₁, f', ?_, hh1'⟩
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hA₀
  rw [Mat.mul_inv_rev, Mat.inv_inv hT.det_ne, ← mul_assoc, Mat.mul_inv hA₀d, one_mul]
  exact hT1'

theorem carries_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (S : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult C.Y.Fn) (K : Type) [Field K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp K ⟶ C.Y.X), Tied e C.Y C.π C.f0 S A₀ → (C.Carries p g ↔ ∃ A ∈ S.S (p (IsLocalRing.closedPoint K)), ∃ (φ₁ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) (f₁ : EigFrame Z φ₁ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z)) (h : Mat Dw.mult K), f₁.Coord (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 (A₀ * A⁻¹) ∧ f₁.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g h ∧ Par Dw.mult ⊤ h) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C S A₀ K _ φ x g p hT
  obtain ⟨hA₀, hTied⟩ := hT
  constructor
  · rintro ⟨y, ψ, φ₁, f, t, t', hp, hf, hg⟩
    obtain ⟨T, hT1, hT2, hT3⟩ := (f.tri_iff _ C.f0 t).1 hf
    obtain ⟨h, hh1, hh2, hh3⟩ := (f.tri_iff _ g t').1 hg
    have hsp : p (IsLocalRing.closedPoint K) ⤳ y := by
      have : p (IsLocalRing.closedPoint K) ∈ Set.range (C.Y.X.fromSpecStalk y) := by
        rw [hp]
        exact ⟨spMap ψ (IsLocalRing.closedPoint K), rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have hψ : ψ = (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
      refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
      have e1 := spMap_stalkClosedPointTo p
      have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _ :=
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
      have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) =
          spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
        simp [spMap, Spec.map_comp]
      rw [e3, Category.assoc, e2, e1]
      exact hp.symm
    obtain ⟨A, hA, φ₂, f₁, c1, c2⟩ := exists_adapted C hA₀ hTied g hsp _ f hT1
      (par_of_tri (fun τ i => by rw [hT2]; exact Units.ne_zero _) hT3) (hψ ▸ hh1)
    exact ⟨A, hA, φ₂, f₁, h, c1, c2, par_of_tri (fun τ i => by rw [hh2]; exact Units.ne_zero _) hh3⟩
  · rintro ⟨A, hA, φ₁, f₁, h, h1, h2, h3⟩
    have hgen := Fr.mem_genericPoint hA
    have hP : Par Dw.mult ⊤ (A₀ * A⁻¹) := ((Fr.mem_iff hgen).1 hA₀).mono le_rfl le_top
    refine ⟨_, (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom, φ₁, f₁,
      fun τ i => Units.mk0 _ (Par.diag_ne hP τ i), fun τ i => Units.mk0 _ (Par.diag_ne h3 τ i),
      (spMap_stalkClosedPointTo p).symm, (f₁.tri_iff _ C.f0 _).2 ⟨_, h1, fun _ _ => rfl, fun τ i k hik => (hP τ).2.2.2 i k i.2 hik⟩,
      (f₁.tri_iff _ g _).2 ⟨h, h2, fun _ _ => rfl, fun τ i k hik => (h3 τ).2.2.2 i k i.2 hik⟩⟩

end GlobalTheory.ShFam.CarriesAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernConnectionCurvaturePolyRepEval
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped Matrix

namespace GlobalTheory.GoodMetric

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]


omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem contDiffAt_aeval_int {σ : Type} {k : WithTop ℕ∞} {f : E → σ → ℂ} {z : E}
    (hf : ∀ s, ContDiffAt ℝ k (fun x => f x s) z) (P : MvPolynomial σ ℤ) :
    ContDiffAt ℝ k (fun x => aeval (f x) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; exact contDiffAt_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p s hp => simp only [map_mul, aeval_X]; exact hp.mul (hf s)

theorem del_aeval_int {σ : Type} [Fintype σ] {f : E → σ → ℂ} {z : E}
    (hf : ∀ s, ContDiffAt ℝ 1 (fun x => f x s) z) (P : MvPolynomial σ ℤ) (ξ : E) :
    del (fun x => aeval (f x) P) z ξ = ∑ s, aeval (f z) (pderiv s P) * del (fun x => f x s) z ξ := by
  classical
  have hd : ∀ Q : MvPolynomial σ ℤ, DifferentiableAt ℝ (fun x => aeval (f x) Q) z :=
    fun Q => (contDiffAt_aeval_int hf Q).differentiableAt one_ne_zero
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, pderiv_C, del_const]; simp
  | add p q hp hq =>
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib, ← hp, ← hq]
    rw [del_add (hd p) (hd q)]; rfl
  | mul_X p s hp =>
    simp only [map_mul, aeval_X]
    rw [del_mul (hd p) ((hf s).differentiableAt one_ne_zero), hp]
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add (f := _), map_mul, aeval_X, add_mul,
      Finset.sum_add_distrib, Finset.sum_mul, Pi.single_apply]
    congr 1
    · rw [Finset.sum_eq_single s] <;> simp +contextual [eq_comm]
    · exact Finset.sum_congr rfl fun _ _ => by ring

variable {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m)

theorem PolyRep.conn_ev {G : E → Mat m ℂ} {u : E} (h : ∀ τ, MContDiffAt 1 (fun w => G w τ) u)
    (hu : ∀ τ, (G u τ).det ≠ 0) (ξ : E) :
    conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ) := by
  set B : Mat m ℂ := (fun τ => (G u τ)ᵀ)⁻¹ with hB
  have hBu : B * (fun τ => (G u τ)ᵀ) = 1 := Mat.inv_mul fun τ => by rw [Matrix.det_transpose]; exact hu τ
  have hev : ∀ w, ρ.ev (B * fun τ => (G w τ)ᵀ) = ρ.ev B * (ρ.ev (G w))ᵀ := fun w => by
    rw [PolyRep.ev, ρ.mul, ρ.transp]; rfl
  have hinv : (ρ.ev (G u))ᵀ⁻¹ = ρ.ev B :=
    Matrix.inv_eq_left_inv (by rw [← hev, hBu]; exact ρ.one ℂ)
  have hρ : MContDiffAt 1 (fun w => ρ.ev (G w)) u := fun i j =>
    contDiffAt_aeval_int (f := fun w (v : EntIx m) => G w v.1 v.2.1 v.2.2) (fun v => h v.1 v.2.1 v.2.2) _
  have hK : ∀ τ, MContDiffAt 1 (fun w => B τ * (G w τ)ᵀ) u := fun τ =>
    (mContDiffAt_const _).mul (h τ).transpose
  have e1 : conn (fun w => ρ.ev (G w)) u ξ = mdel (fun w => ρ.ev (B * fun τ => (G w τ)ᵀ)) u ξ := by
    simp only [hev]
    rw [mdel_mul (mContDiffAt_const _) hρ.transpose, mdel_const, Matrix.zero_mul, add_zero, conn, hinv]
    rfl
  have e2 : ∀ τ, conn (fun w => G w τ) u ξ = mdel (fun w => B τ * (G w τ)ᵀ) u ξ := fun τ => by
    rw [mdel_mul (mContDiffAt_const _) (h τ).transpose, mdel_const, Matrix.zero_mul, add_zero, conn]
    rfl
  rw [e1]
  simp only [e2]
  ext i j
  refine (del_aeval_int (f := fun w (v : EntIx m) => (B * fun τ => (G w τ)ᵀ : Mat m ℂ) v.1 v.2.1 v.2.2)
    (fun v => hK v.1 v.2.1 v.2.2) (ρ.ent i j) ξ).trans ?_
  rw [hBu]
  rfl

theorem PolyRep.mdbar_lie {A : E → Mat m ℂ} {u : E} (h : ∀ τ, MContDiffAt 1 (fun w => A w τ) u) (η : E) :
    mdbar (fun w => ρ.lie (A w)) u η = ρ.lie (fun τ => mdbar (fun w => A w τ) u η) := by
  ext i j
  simp only [mdbar_apply, PolyRep.lie, Matrix.of_apply]
  rw [dbar_sum fun v _ => (differentiableAt_const _).fun_mul ((h v.1).diff v.2.1 v.2.2),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dbar_mul (differentiableAt_const _) ((h v.1).diff v.2.1 v.2.2)]
  simp

theorem PolyRep.eventually_conn_ev {G : E → Mat m ℂ} {v : E} (h : ∀ τ, MContDiffAt 2 (fun w => G w τ) v)
    (hv : ∀ τ, (G v τ).det ≠ 0) :
    ∀ᶠ u in 𝓝 v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ) := by
  filter_upwards [eventually_all.2 fun τ => (h τ).eventually_two,
    eventually_all.2 fun τ => (h τ).eventually_isUnit (hv τ).isUnit] with u h1 h2 ξ
  exact ρ.conn_ev (fun τ => (h1 τ).of_le one_le_two) (fun τ => (h2 τ).ne_zero) ξ

theorem PolyRep.curv_ev {G : E → Mat m ℂ} {v : E} (h : ∀ τ, MContDiffAt 2 (fun w => G w τ) v)
    (hv : ∀ τ, (G v τ).det ≠ 0) (ξ η : E) :
    curv (fun w => ρ.ev (G w)) v ξ η = ρ.lie (fun τ => curv (fun w => G w τ) v ξ η) := by
  rw [curv, mdbar_congr ((ρ.eventually_conn_ev h hv).mono fun u hu => hu ξ),
    ρ.mdbar_lie (A := fun u τ => conn (fun w => G w τ) u ξ)
      (fun τ => (h τ).conn (hv τ).isUnit (by norm_num) ξ)]
  ext i j
  simp [PolyRep.lie, curv]

end General

theorem PolyRep.lie_sum_C_mul_X {ι κ : Type} [Fintype ι] [Fintype κ] {m : ι → ℕ} (ρ : PolyRep m)
    (F : κ → κ → Mat m ℂ) :
    (Matrix.of fun i j => ∑ a, ∑ b, C (ρ.lie (F a b) i j) * X (a, b) : Matrix _ _ (MvPolynomial (κ × κ) ℂ)) =
      ρ.lie fun τ => Matrix.of fun i j => ∑ a, ∑ b, C (F a b τ i j) * X (a, b) := by
  have hc : ∀ (S : Type) [CommRing S] (φ : ℂ →+* S) (P : MvPolynomial (EntIx m) ℤ),
      aeval (fun w : EntIx m => (1 : Mat m S) w.1 w.2.1 w.2.2) P =
        φ (aeval (fun w : EntIx m => (1 : Mat m ℂ) w.1 w.2.1 w.2.2) P) := fun S _ φ P => by
    induction P using MvPolynomial.induction_on with
    | C a => rw [aeval_C, aeval_C, eq_intCast, eq_intCast, map_intCast]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | mul_X p s hp =>
      rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X, Pi.one_apply, Pi.one_apply, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs
      · rw [map_one]
      · rw [map_zero]
  refine Matrix.ext fun i j => ?_
  have key : ∀ (c : EntIx m → ℂ) (f : κ → κ → EntIx m → ℂ),
      (∑ a, ∑ b, C (∑ v, c v * f a b v) * X (a, b) : MvPolynomial (κ × κ) ℂ) =
        ∑ v, C (c v) * ∑ a, ∑ b, C (f a b v) * X (a, b) := fun c f => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [eq_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  simp only [PolyRep.lie, Matrix.of_apply]
  rw [key]
  exact Finset.sum_congr rfl fun v _ => by rw [hc _ C]

theorem conn_curvPoly_ev : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (n : ℕ) (G : V n → Mat m ℂ) (v : V n),
    (∀ τ, MContDiffAt 2 (fun u => G u τ) v) → (∀ τ, (G v τ).det ≠ 0) →
    (∀ᶠ u in nhds v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ)) ∧
      curvPoly (fun w => ρ.ev (G w)) v = ρ.lie (fun τ => curvPoly (fun w => G w τ) v) := by
  intro ι _ m ρ n G v h hv
  refine ⟨ρ.eventually_conn_ev h hv, ?_⟩
  simp only [curvPoly, ρ.curv_ev h hv]
  exact ρ.lie_sum_C_mul_X fun a b τ => curv (fun w => G w τ) v (coordVec a) (coordVec b)

end GlobalTheory.GoodMetric

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct Topology GlobalTheory.AffinePoints

namespace GlobalTheory.CxPtsDense

open GlobalTheory.CxPts

variable {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F) (σ : F →+* ℂ)

theorem exists_param [GeometricallyIntegral p] [LocallyOfFiniteType p] {U : X.Opens} (hU : IsAffineOpen U)
    {f : Γ(X, U)} (hf : f ≠ 0) :
    ∃ (B : Type) (_ : TopologicalSpace B) (s : B → CxPts p σ), Nonempty B ∧ Continuous s ∧
      ptsIn p σ U ⊆ Set.range s ∧ Dense (s ⁻¹' ptsIn p σ (X.basicOpen f)) := by
  let : Algebra F Γ(X, U) := (algX p U).toAlgebra
  let : Algebra F ℂ := σ.toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType F Γ(X, U) := hft
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have : Nontrivial Γ(X, U) := nontrivial_of_ne _ _ hf
  have : NoZeroDivisors (ℂ ⊗[F] Γ(X, U)) :=
    @UnitRigidity.noZeroDivisors_tensor F Γ(X, U) _ _ _ (algX p U).toAlgebra X p _
      hU.fromSpec (inferInstanceAs (IsOpenImmersion hU.fromSpec)) hg ℂ _ _
  have hinj := Algebra.TensorProduct.includeRight_injective (R := F) (A := ℂ) (B := Γ(X, U))
      (algebraMap F ℂ).injective
  have : Nontrivial (ℂ ⊗[F] Γ(X, U)) := hinj.nontrivial
  have : IsDomain (ℂ ⊗[F] Γ(X, U)) := NoZeroDivisors.to_isDomain _
  let φ (q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ) : Γ(X, U) →+* ℂ :=
    q.toRingHom.comp (Algebra.TensorProduct.includeRight (R := F) (A := ℂ)).toRingHom
  have hφa (q) (a) : φ q a = q (1 ⊗ₜ a) := rfl
  have hφ (q) (a : F) : φ q (algX p U a) = σ a := by
    have : ((1 : ℂ) ⊗ₜ[F] algX p U a) = algebraMap ℂ (ℂ ⊗[F] Γ(X, U)) (σ a) :=
      (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := F) (A := ℂ) (B := Γ(X, U)) a).symm
    rw [hφa, this, AlgHom.commutes]
    rfl
  let s (q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ) : CxPts p σ := ofHom hU (φ q) (hφ q)
  have hsU (q) : s q ∈ ptsIn p σ U := ofHom_mem _ _ _
  have hsv (q) (a) : ev p σ U a (s q) = q (1 ⊗ₜ a) := ev_ofHom _ _ _ a
  refine ⟨_, inferInstance, s, ?_, ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal (ℂ ⊗[F] Γ(X, U))
    let := Ideal.Quotient.field m
    have : Module.Finite ℂ ((ℂ ⊗[F] Γ(X, U)) ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
    exact ⟨(IsAlgClosed.lift (R := ℂ) (S := (ℂ ⊗[F] Γ(X, U)) ⧸ m) (M := ℂ)).comp (Ideal.Quotient.mkₐ ℂ m)⟩
  · refine continuous_iff_continuousAt.2 fun q => tendsto_subtype_rng.2
      (GlobalTheory.Points.tendsto_of_isAffineOpen hU (hsU q) (Filter.Eventually.of_forall hsU) fun a => ?_)
    have h : Continuous (ev p σ U a ∘ s) := by
      have : ev p σ U a ∘ s = fun q => q (1 ⊗ₜ a) := funext fun q => hsv q a
      rw [this]
      exact GlobalTheory.AffinePoints.continuous_eval _
    exact h.continuousAt
  · let ψ : Γ(X, U) →ₐ[F] ℂ :=
      { evHom hy with commutes' := fun a => (ev_eq hy _).symm.trans (ev_algX hy a) }
    let q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ :=
      Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) ψ fun _ _ => Commute.all _ _
    refine ⟨q, Subtype.ext (GlobalTheory.Points.ext_of_valR hU (hsU q) hy fun a => ?_)⟩
    refine (hsv q a).trans ?_
    simp only [q, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact (ev_eq hy a).symm
  · have hf' : ((1 : ℂ) ⊗ₜ[F] f) ≠ 0 := (map_ne_zero_iff _ hinj).2 hf
    refine (GlobalTheory.AffinePoints.dense_nonvanishing hf').mono fun q hq => ?_
    refine (mem_ptsIn_basicOpen (hsU q) f).2 ?_
    rw [hsv]
    exact hq

theorem exists_ne_zero_basicOpen_le [IsIntegral X] {U W : X.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set X).Nonempty) (hW : (W : Set X).Nonempty) :
    ∃ f : Γ(X, U), f ≠ 0 ∧ X.basicOpen f ≤ W := by
  obtain ⟨x, hxU, hxW⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen hne hW
  obtain ⟨f, hfW, hf⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU
  refine ⟨f, ?_, hfW⟩
  rintro rfl
  rw [Scheme.basicOpen_zero] at hf
  exact hf

theorem nonempty_and_dense_of_geometricallyIntegral [GeometricallyIntegral p] [LocallyOfFiniteType p] :
    Nonempty (CxPts p σ) ∧ ∀ W : X.Opens, (W : Set X).Nonempty → Dense (ptsIn p σ W) := by
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton p
  refine ⟨?_, fun W hW y => ?_⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top (genericPoint X))
    obtain ⟨f, hf, -⟩ := exists_ne_zero_basicOpen_le hU ⟨_, hx⟩ ⟨_, hx⟩
    obtain ⟨B, _, s, ⟨b⟩, -⟩ := exists_param p σ hU hf
    exact ⟨s b⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ)))
    obtain ⟨f, hf, hfW⟩ := exists_ne_zero_basicOpen_le hU ⟨_, hx⟩ hW
    obtain ⟨B, _, s, -, hs, hr, hd⟩ := exists_param p σ hU hf
    obtain ⟨b, rfl⟩ := hr (mem_ptsIn.2 hx)
    exact closure_mono (ptsIn_mono hfW) (hs.closure_preimage_subset _ (hd b))

theorem nonempty_and_dense : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ),
    Nonempty (CxPts Y.str σ) ∧ ∀ W : Y.X.Opens, (W : Set Y.X).Nonempty → Dense (CxPts.ptsIn Y.str σ W) :=
  fun _ _ Y σ => nonempty_and_dense_of_geometricallyIntegral Y.str σ

end GlobalTheory.CxPtsDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeBaseChangeLocalRings
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom.Vanish

open GlobalTheory.ShFam.Descent GlobalTheory.FlagTan GlobalTheory.AllWt GlobalTheory.Cartier

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

def FrameBC (Z : Model Xo c β) : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X)
    (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x),
      ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i

theorem FrameBC.at (hbc : FrameBC Z) {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') {x' : Sp R' ⟶ Z.X}
    (hx : x' = spMap ψ ≫ x) : ∃ g : EigFrame Z (ψ.comp φ) x', ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
  subst hx
  exact hbc R R' φ x f ψ

section Cpt

variable {C : FlagCpt Z e}

end Cpt

section Core

end Core

end GlobalTheory.CuspFrom.Vanish

namespace GlobalTheory.CuspFrom

end GlobalTheory.CuspFrom
end
end

