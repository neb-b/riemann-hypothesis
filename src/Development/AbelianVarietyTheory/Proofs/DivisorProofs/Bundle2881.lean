module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2867

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenRankInteriorEqSignature
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BalProjInt

open GlobalTheory.ShFam.Pad GlobalTheory.ArLieBase GlobalTheory.BalProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tan_act {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x0 : Sp S ⟶ X} (a : 𝓞 E)
    {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : IsTanAtG t x0 (v ≫ (t.act.act a).left) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, Over.w]; exact hv.1
  · rw [← Category.assoc, hv.2, ← Over.comp_left]
    congr 1
    haveI := t.act.hom a
    rw [Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem comb_act_mat {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x0 : Sp S ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hu : ∀ i, IsTanAtG t x0 (u i)) (a : 𝓞 E)
    {B : Matrix (Fin m) (Fin m) S} (hB : ∀ i, IsCombAtG t x0 u (B i) (u i ≫ (t.act.act a).left))
    {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsCombAtG t x0 u cf w) :
    IsCombAtG t x0 u (cf ᵥ* B) (w ≫ (t.act.act a).left) := by
  have := t.act.hom a
  have hu' := fun i => tan_act t a (hu i)
  have h2 : IsCombAtG t x0 (fun i => u i ≫ (t.act.act a).left) cf (w ≫ (t.act.act a).left) := by
    have h1 := (isCombAtG_iff t x0 (fun j => ovT (hu j)) cf w).1 hw
    refine (isCombAtG_iff t x0 (fun j => ovT (hu' j)) cf _).2 ?_
    rw [← h1, ← Over.comp_left, combT_post]
    congr 2
  have h3 := tanLinG u hu _ Bᵀ cf _ (fun i => hB i) h2
  rwa [Matrix.mulVec_transpose] at h3

theorem affineOpenChart_comp_structure_eq_spMap {K : Type} [CommRing K] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of K)) (U : X.affineOpens) :
    chart U ≫ s = spMap (fnHom s U.1) := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Spec (CommRingCat.of K))) U.2
    (le_top : U.1 ≤ s ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  rw [chart, ← e, ← Spec.map_comp]
  rfl

theorem exists_eig_subspace_gen {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Z : Model Xo c β) {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)) (he : GlobalTheory.LineNorm.IsTanBasis Z.t x e) (K : Type) [Field K]
    (ψ : R →+* K) (φ : c.F →+* K) (hφ : spMap ψ ≫ x ≫ Z.s = spMap (φ.comp β)) :
    ∃ V : Submodule K (Fin g → K), Module.finrank K V = Dw.mult τ ∧
      ∀ (cf : Fin g → K) (w : Sp (DualNumber K) ⟶ Z.t.G.left),
        IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w →
          (IsEigTan Z φ (spMap ψ ≫ x) τ w ↔ cf ∈ V) := by
  have h0 : (spMap ψ ≫ x) ≫ Z.s = spMap φ ≫ spMap β := by
    rw [Category.assoc, hφ, Guard.sp_comp]
  let y : Sp K ⟶ gen Z := Limits.pullback.lift (spMap ψ ≫ x) (spMap φ) h0
  have hy1 : y ≫ genι Z = spMap ψ ≫ x := Limits.pullback.lift_fst _ _ _
  have hy2 : y ≫ genStr Z = spMap φ := Limits.pullback.lift_snd _ _ _
  have hf := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c _ _ Z K φ y hy2
  rw [hy1] at hf
  obtain ⟨f⟩ := hf
  have hv : ∀ i, IsTanAtG Z.t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ e i) :=
    fun i => GlobalTheory.FactorDepth.isTanAtG_map Z.t ψ (he.1 i)
  have hb := he.2 K ψ
  choose a ha using fun i => (hb _ (f.tan τ i)).exists
  let A : Matrix (Fin g) (Fin (Dw.mult τ)) K := fun j i => a i j
  have heig : ∀ cf w, IsCombAtG Z.t (spMap ψ ≫ x) (f.v τ) cf w → ∀ b : 𝓞 E,
      w ≫ (Z.t.act.act b).left = spMap (epsMul (φ (embK c τ b))) ≫ w := fun cf w h1 b => by
    rw [← (isCombAtG_iff Z.t _ (fun j => ovT (f.tan τ j)) _ _).1 h1]
    have := Z.t.act.hom b
    exact congrArg (fun f => f.left) (combT_eig _ (fun j => ovT (f.tan τ j)) (Z.t.act.act b) _
      (fun j => Over.OverMorphism.ext (f.eig τ j b)) cf)
  have hi : Guard.Indep Z.t (spMap ψ ≫ x) (f.v τ) := fun cf cf' w h1 h2 =>
    (f.basis τ w (Guard.comb_tan (f.tan τ) h1) (heig cf w h1)).unique h1 h2
  have hinj := (Guard.indep_iff hv (Guard.indep_of_basis hv hb) A ha).1 hi
  refine ⟨LinearMap.range A.mulVecLin, ?_, fun cf w hw => ⟨fun h => ?_, ?_⟩⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  · obtain ⟨b, hb', -⟩ := f.basis τ w h.1 h.2
    exact ⟨b, (hb w h.1).unique (tanLinG _ hv (f.v τ) A b w ha hb') hw⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨w', h1, h2⟩ := Guard.exists_comb (f.tan τ) b
    obtain rfl : w' = w := Guard.comb_unique hv (tanLinG _ hv (f.v τ) A b w' ha h2) hw
    exact ⟨h1, heig b w' h2⟩

theorem mem_eigSp {O k : Type} [Field k] {n : ℕ} (B : O → Matrix (Fin n) (Fin n) k) (χ : O → k) (c : Fin n → k) :
    c ∈ eigSp B χ ↔ ∀ a, c ᵥ* B a = χ a • c := Iff.rfl

theorem eigRank_field {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left))
    (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (hv : ∀ i, IsTanAtG Y.t (chart U) (v i))
    (hb : ∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w)
    (hA : ∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) (K : Type) [Field K]
    (ψ : Γ(Y.X, U.1) →+* K) (τ : E →+* ℂ) :
    eigRank ψ A (embR c.F c.conj (fnHom Y.s U.1) τ) = Dw.mult τ := by
  let φ : c.F →+* K := ψ.comp (fnHom Y.s U.1)
  have he := GlobalTheory.LineNorm.isTanBasis_of_basis E H Y.X Y.t Γ(Y.X, U.1) (chart U) n v hv hb
  have hφ : spMap ψ ≫ chart U ≫ Y.s = spMap (φ.comp (RingHom.id c.F)) := by
    rw [affineOpenChart_comp_structure_eq_spMap, Guard.sp_comp]
  obtain ⟨V, hVr, hV⟩ := exists_eig_subspace_gen Y (chart U) τ v he K ψ φ hφ
  have hvK : ∀ i, IsTanAtG Y.t (spMap ψ ≫ chart U) (spMap (dualMap ψ) ≫ v i) :=
    fun i => GlobalTheory.FactorDepth.isTanAtG_map Y.t ψ (hv i)
  have hbK := he.2 K ψ
  have hAK : ∀ a i, IsCombAtG Y.t (spMap ψ ≫ chart U) (fun j => spMap (dualMap ψ) ≫ v j) ((A a).map ψ i)
      ((spMap (dualMap ψ) ≫ v i) ≫ (Y.t.act.act a).left) := fun a i => by
    rw [Category.assoc]
    exact GlobalTheory.LatDRFree.comb_map Y.t ψ (hA a i)
  have key : eigSp (fun a => (A a).map ψ) (fun a => ψ (embR c.F c.conj (fnHom Y.s U.1) τ a)) = V := by
    ext cf
    obtain ⟨w, -, hw⟩ := Guard.exists_comb hvK cf
    rw [← hV cf w hw]
    have hs : ∀ a : 𝓞 E, ψ (embR c.F c.conj (fnHom Y.s U.1) τ a) • cf = fun k => φ (embK c τ a) * cf k :=
      fun a => rfl
    rw [mem_eigSp]
    constructor
    · intro h
      refine ⟨Guard.comb_tan hvK hw, fun a => ?_⟩
      have h1 := comb_act_mat Y.t hvK a (hAK a) hw
      rw [h a, hs a] at h1
      exact Guard.comb_unique hvK h1 (Guard.comb_smul hvK hw (φ (embK c τ a)))
    · rintro ⟨-, h⟩ a
      have h1 := comb_act_mat Y.t hvK a (hAK a) hw
      have h2 := Guard.comb_smul hvK hw (φ (embK c τ a))
      rw [← h a] at h2
      rw [hs a]
      exact (hbK _ (Guard.comb_tan hvK h1)).unique h1 h2
  unfold eigRank
  rw [key, hVr]

end GlobalTheory.BalProjInt

theorem GlobalTheory.BalProjInt.eigRank_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (𝔭 : PrimeSpectrum Γ(Y.X, U.1)), (chart U).base 𝔭 ∈ (interior Y : Set Y.X) → ∀ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) 𝔭.asIdeal.ResidueField) A (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ) = if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q := by
  intro E _ _ _ H Dw l Xo c Y _ _ _ U n v A hv hb hA 𝔭 _ τ
  exact GlobalTheory.BalProjInt.eigRank_field Y U n v A hv hb hA _ _ τ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedBoundaryPointMaximalIdeal
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer

namespace GlobalTheory.BoundaryPoint

theorem isClosed_of_isMaximal {X : Scheme.{0}} [JacobsonSpace X] {U : X.Opens} (hU : IsAffineOpen U)
    {m : Ideal Γ(X, U)} (hm : m.IsMaximal) {x : X} (hx : x ∈ U) (h : ∀ f ∈ m, x ∉ X.basicOpen f) :
    IsClosed ({x} : Set X) := by
  have e := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have hle : m ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := fun f hf => by
    by_contra hc
    refine h f hf ?_
    have h₁ : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact hc
    have h₂ : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := h₁
    rwa [e] at h₂
  have hmax : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.IsMaximal :=
    hm.eq_of_le (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top hle ▸ hm
  have hc := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hmax
  have h₃ : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹' closedPoints X := by
    rw [hU.fromSpec.isOpenEmbedding.preimage_closedPoints]
    exact hc
  have h₄ : IsClosed ({hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩)} : Set X) := h₃
  rwa [e] at h₄

theorem exists_closed_boundary_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U : Y.X.affineOpens) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → ∃ x' : gen Y, genι Y x' = x ∧ x' ∈ genBd Y ∧ IsClosed ({x'} : Set (gen Y)) := by
  intro E _ _ _ H Dw l Xo c Y hs U m hm x hx hU h
  have hi : IsIso (genι Y) := GlobalTheory.LogKS.isIso_fst Y
  have : Smooth (genStr Y) := SmoothOfRelativeDimension.smooth Dw.dim _
  have : JacobsonSpace Y.X := LocallyOfFiniteType.jacobsonSpace (inv (genι Y) ≫ genStr Y)
  have hc := isClosed_of_isMaximal U.2 hm hU h
  obtain ⟨x', rfl⟩ := (genι Y).homeomorph.surjective x
  refine ⟨x', rfl, mem_genBd_iff.2 fun h' => hx ?_, ?_⟩
  · rw [← coe_interior] at h'
    exact h'
  · rw [← (genι Y).homeomorph.isClosed_image, Set.image_singleton]
    exact hc

end GlobalTheory.BoundaryPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfMemHodgeFiltration
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.OrthPt

variable {R : Type} [CommRing R]

theorem iSup_parCov {A B : Over (Sp R)} {K : Type} {W : K → (A ⊗ B).left.Opens} (hW : ⨆ i, W i = ⊤)
    {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) : ⨆ i, parCov W x i = ⊤ := by
  unfold parCov
  exact (x ▷ B).left.iSup_preimage_eq_top hW

theorem sm_parCov {A B : Over (Sp R)} {K : Type} {W : K → (A ⊗ B).left.Opens}
    {D D' E : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing E] [Algebra R E]
    (φ : D →ₐ[R] D') (x : Pt A D) (z : Pt (SpAlg R D' ⊗ B) E) (h : Sm (parCov W (spOver φ ≫ x)) z) :
    Sm (parCov W x) (z ≫ spOver φ ▷ B) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  unfold parCov at hi ⊢
  rw [comp_whiskerRight, Over.comp_left, Scheme.Hom.comp_preimage] at hi
  rw [Over.comp_left, Scheme.Hom.comp_preimage]
  exact hi

theorem sumMul_elim {B : Over (Sp R)} {D : Type} [CommRing D] [Algebra R D] {I₁ I₂ I₃ : Type} [Fintype I₁]
    [Fintype I₂] [Fintype I₃] (d₁ : I₁ → D) (d₂ : I₂ → D) (d₃ : I₃ → D)
    (β₁ : I₁ → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (β₂ : I₂ → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))
    (β₃ : I₃ → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))
    (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E')
    (z : Pt (SpAlg R D ⊗ B) E) :
    sumMul (Sum.elim d₁ (Sum.elim (fun i ↦ -d₂ i) (fun i ↦ -d₃ i)))
        (fun i ↦ fv (Sum.elim β₁ (Sum.elim β₂ β₃) i)) E E' ψ z =
      sumMul d₁ (fun i ↦ fv (β₁ i)) E E' ψ z - sumMul d₂ (fun i ↦ fv (β₂ i)) E E' ψ z -
        sumMul d₃ (fun i ↦ fv (β₃ i)) E E' ψ z := by
  simp only [sumMul, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_neg, neg_mul, Finset.sum_neg_distrib]
  ring

theorem exists_isCob_of_mem_fil : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ (K : Type) (W : K → (A ⊗ B).left.Opens), ⨆ i, W i = ⊤ → ∀ (J : Type) [Fintype J] (a : J → Fn1 A) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (hβ : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B) (n : Fn1 (A ⊗ B)), (∀ i, IsCoc (whole A) (a i)) → IsCupCob W a (fun i ↦ fv (β i)) n → ∀ y ∈ Fil B, ∃ k : Fn0 A, IsCob (whole A) (fun D _ _ D' _ _ φ x ↦ ∑ i, a i D D' φ x * algebraMap R D' (y ⟨_, hβ i⟩)) k := by
  intro H R _ A B _ g hB hg K W hW J _ a β hβ n ha hn y hy
  have hP : ∀ f : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f ∈ primDR B := fun f ↦ by
    have h : primDR B = ⊤ := ((GlobalTheory.abelianDeRham_free_baseChange_rigid H).1 R B g hB hg).1
    rw [h]; trivial
  have hfv : ∀ f : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)), IsCoc (whole B) (fv f) := fun f ↦ (fv_isCoc_and_ev_eq R B f).1
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      ∃ (m : ℕ) (d : Fin m → D) (c : Fin m → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (k : Fn0 (SpAlg R D ⊗ B)),
        IsCob (parCov W x) ((parCoc a (fun i ↦ fv (β i)) n x).add (sumMul d fun i ↦ fv (c i)).neg) k := by
    intro D _ _ x
    obtain ⟨u, hu, k₁, h₁⟩ := _root_.GlobalTheory.PtExt.CocExt.cocycle_extends R _ K (parCov W x) (iSup_parCov hW x) _
      (GlobalTheory.PtExt.parCoc_isCoc R A B K W J a _ n ha (fun i ↦ hfv _) hn D x)
    obtain ⟨m, d, c, k₂, h₂⟩ := _root_.GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian H R B g hB hg D u hu
    refine ⟨m, d, c, fun E _ _ z ↦ k₁ E z + k₂ E z, ?_⟩
    intro E _ _ E' _ _ ψ z hz
    have e₁ := h₁ E E' ψ z hz
    have e₂ := h₂ E E' ψ z (sm_whole z)
    simp only [Fn1.add, Fn1.neg] at e₁ e₂ ⊢
    rw [map_add (f := _)]
    linear_combination e₁ + e₂
  choose m d c k hk using key
  refine ⟨fun D _ _ x ↦ ∑ j, d D x j * algebraMap R D (y ⟨_, hP (c D x j)⟩), ?_⟩
  intro D _ _ D' _ _ φ x _
  have hcob : IsCob (parCov W (spOver φ ≫ x))
      (sumMul (Sum.elim (d D' (spOver φ ≫ x)) (Sum.elim (fun i ↦ -φ (d D x i)) (fun i ↦ -a i D D' φ x)))
        (fun i ↦ fv (Sum.elim (c D' (spOver φ ≫ x)) (Sum.elim (c D x) β) i)))
      (fun E _ _ z ↦ k D x E (z ≫ spOver φ ▷ B) - k D' (spOver φ ≫ x) E z) := by
    intro E _ _ E' _ _ ψ z hz
    have e₁ := hk D' (spOver φ ≫ x) E E' ψ z hz
    have e₂ := hk D x E E' ψ (z ≫ spOver φ ▷ B) (sm_parCov φ x z hz)
    have e₃ := congrArg (fun u : Fn1 (SpAlg R D' ⊗ B) ↦ u E E' ψ z)
      (GlobalTheory.PtExt.parCoc_spOver R A B J a (fun i ↦ fv (β i)) n ha D D' φ x)
    have e₄ := congrArg (fun u : Fn1 (SpAlg R D' ⊗ B) ↦ u E E' ψ z)
      ((GlobalTheory.PtExt.SumMulFacts.main R D B _ (d D x) (fun i ↦ fv (c D x i))).2 D' φ)
    rw [sumMul_elim]
    simp only [Fn1.add, Fn1.neg, Fn1.pull] at e₁ e₂ e₃ e₄
    beta_reduce
    rw [map_sub, Category.assoc]
    linear_combination e₂ - e₁ + e₃ + e₄
  have h0 := _root_.GlobalTheory.PtExt.sum_mul_eq_zero_of_isCob H R B g hB hg y hy D' _ _ _ (fun i ↦ hP _)
    (GlobalTheory.PtExt.isCob_whole_of_isCob_cover R _ K _ (iSup_parCov hW (spOver φ ≫ x)) _
      ((GlobalTheory.PtExt.SumMulFacts.main R D' B _ _ _).1 fun i ↦ hfv _) _ hcob)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, AlgHom.commutes]
  linear_combination -h0

end GlobalTheory.PtExt.OrthPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffsTangentVectorTranslatedBasis
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertSpan

theorem exists_coeffs_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ → w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom → ∃ c : Fin n → S, ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = ∑ a, ρ (c a) * (valR (wt a) O f).snd := by
  intro E _ _ _ H X t U n v hv hb S _ φ g₀ w hg hred hw
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [GlobalTheory.LogKSLoc.spMap_comp', ← Spec.map_id]
    congr 1
  let g' : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g₀) (Category.assoc _ _ _)
  let w' : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G := Over.homMk w hw
  let s : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      change _ ≫ _ ≫ _ = g₀ ≫ t.G.hom
      rw [← Category.assoc, e, Category.id_comp])
  have hs : s ≫ g' = s ≫ w' := by
    refine Over.OverMorphism.ext ?_
    change spMap _ ≫ spMap _ ≫ g₀ = spMap _ ≫ w
    rw [hred, ← Category.assoc, e, Category.id_comp]
  have hτ : IsTanAtG t (g₀ ≫ t.G.hom) (g'⁻¹ * w').left := by
    refine ⟨Over.w (g'⁻¹ * w'), ?_⟩
    change (s ≫ (g'⁻¹ * w')).left = _
    rw [MonObj.comp_mul, GrpObj.comp_inv, hs, inv_mul_cancel]
  have hbas := (GlobalTheory.LineNorm.isTanBasis_of_basis E H X t _ (chart U) n v hv hb).2 S φ (g'⁻¹ * w').left
  rw [← hg] at hbas
  obtain ⟨c, ⟨u, hu, hux⟩, -⟩ := hbas hτ
  have hwu : w' = g' * (List.ofFn u).prod := by
    rw [show (List.ofFn u).prod = g'⁻¹ * w' from Over.OverMorphism.ext hux, mul_inv_cancel_left]
  refine ⟨c, fun S' _ ρ φ' wt hg' hwt O hO f => ?_⟩
  have h₃ : (spMap ρ ≫ g₀) ≫ t.G.hom = spMap (ρ.comp φ) ≫ chart U := by
    rw [Category.assoc, hg, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp']
  have hU : ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    change ⊤ ≤ ((spMap ρ ≫ g₀) ≫ t.G.hom) ⁻¹ᵁ U.1
    rw [hg']
    exact GlobalTheory.Points.le_preimage_specMap_fromSpec U.2 (CommRingCat.ofHom φ')
  obtain rfl : φ' = ρ.comp φ := RingHom.ext fun r =>
    (GlobalTheory.LogKSLin.valR_base U le_rfl hg' hU r).symm.trans (GlobalTheory.LogKSLin.valR_base U le_rfl h₃ hU r)
  choose g'' v'' hg'' hv'' hw'' using hwt
  have e' : spMap (dualMap ρ) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ρ := by
    rw [GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp']
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let k : tEpsG ((spMap ρ ≫ g₀) ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) := Over.homMk (spMap (dualMap ρ)) (by
    change _ ≫ _ ≫ _ = _ ≫ (_ ≫ _) ≫ _
    rw [← Category.assoc, e']
    simp only [Category.assoc])
  have hkg : (k ≫ g').left = spMap (algebraMap S' (DualNumber S')) ≫ spMap ρ ≫ g₀ := by
    change spMap _ ≫ spMap _ ≫ g₀ = _
    rw [← Category.assoc, e', Category.assoc]
  have hgg : ∀ a, g'' a = k ≫ g' := fun a => Over.OverMorphism.ext ((hg'' a).trans hkg.symm)
  have hy0 : ∀ a, smT ((spMap ρ ≫ g₀) ≫ t.G.hom) 0 (v'' a) = 1 := fun a => by
    have ht := GlobalTheory.LieMet.isTan_map (ρ.comp φ) h₃.symm (hv a)
    rw [show v'' a = ovT ht from Over.OverMorphism.ext (hv'' a)]
    exact smT_zero_ovT ht
  have hku : ∀ a, k ≫ u a = smT ((spMap ρ ≫ g₀) ≫ t.G.hom) (ρ (c a)) (v'' a) := fun a => by
    refine Over.OverMorphism.ext ?_
    change spMap (dualMap ρ) ≫ (u a).left = spMap (epsMul (ρ (c a))) ≫ (v'' a).left
    rw [hu a, hv'' a]
    simp only [← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap]
    congr 2
    refine RingHom.ext fun z => ?_
    ext <;> simp [epsMul, dualMap]
  have hmain : spMap (dualMap ρ) ≫ w = ((k ≫ g') * (List.ofFn fun a =>
      smT ((spMap ρ ≫ g₀) ≫ t.G.hom) (ρ (c a)) (v'' a)).prod).left := by
    change (k ≫ w').left = _
    rw [hwu, MonObj.comp_mul, GlobalTheory.FirstOrderValue.comp_prod_ofFn]
    simp only [hku]
  rw [hmain]
  refine (GlobalTheory.KSLin.snd_valR_translate_prod _ t.G (spMap ρ ≫ g₀) (k ≫ g') hkg v'' (fun a => ρ (c a)) hy0 O f
    hO).trans (Finset.sum_congr rfl fun a _ => ?_)
  rw [← hw'' a, hgg a]

end GlobalTheory.VertSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionSumWedgeCurvatureAbelianScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem dRel_pO {R : Type} [CommRing R] {Y A : Over (Sp R)} (f : Y ⟶ A) (x : HO1 A.hom) {n : ℕ}
    (y : Fin n → HO1 A.hom) (w : Fin n → GlobForm A.hom) (h : DRel (OAff A.hom) x y w) :
    DRel (OAff Y.hom) (pO1 f x) (fun k ↦ pO1 f (y k)) (fun k ↦ pF f (w k)) :=
  _root_.GlobalTheory.dRel_pull R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f) x n y w h

theorem sum_dRel_eq_zero (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hs : SmoothOfRelativeDimension g A.hom) (x : HO1 A.hom) {n : ℕ} (y : Fin n → HO1 A.hom)
    (w : Fin n → GlobForm A.hom) (hx : DRel (OAff A.hom) x y w) (l : GlobForm A.hom →ₗ[R] R) :
    ∑ k, l (w k) • y k = 0 := by
  obtain ⟨-, -, hA2, hs2⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hs
  obtain ⟨hF2, hC2, -, -⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R (A ⊗ A) (g + g) hA2 hs2
  obtain ⟨hax, hafF, -⟩ := _root_.GlobalTheory.AbCoh.AxesPull.main R A
  have hprim := _root_.GlobalTheory.AbCoh.primO1_of_isAbelianScheme R A g hA hs x
  set a₁ : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  set a₂ : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  have hμ := dRel_pO μ[A] x y w hx
  have hfst := dRel_pO (fst A A) x y w hx
  have hsnd := dRel_pO (snd A A) x y w hx
  have hsum := (_root_.GlobalTheory.AbCoh.rel_add R _ (OAff (A ⊗ A).hom)).1 _ _ _ _ _ _ _ _ hfst hsnd
  rw [← hprim] at hsum
  have key := _root_.GlobalTheory.AbCoh.derivClass_eq R _ (OAff (A ⊗ A).hom) hF2 hC2 _ _ _ _ _ _ _ hμ hsum (l ∘ₗ pF a₂)
  rw [Fin.sum_univ_add] at key
  simp only [LinearMap.comp_apply, Fin.append_left, Fin.append_right] at key
  have e1 : ∀ k, l (pF a₂ (pF μ[A] (w k))) = l (w k) := fun k ↦ by rw [(hafF (w k)).2.2.2.2.2]
  have e2 : ∀ k, l (pF a₂ (pF (fst A A) (w k))) = 0 := fun k ↦ by rw [(hafF (w k)).2.2.2.1, map_zero]
  have e3 : ∀ k, l (pF a₂ (pF (snd A A) (w k))) = l (w k) := fun k ↦ by rw [(hafF (w k)).2.2.2.2.1]
  simp only [e1, e2, e3, zero_smul, Finset.sum_const_zero, zero_add] at key
  have := congrArg (pO1 a₁) key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul] at this
  have f1 : ∀ k, pO1 a₁ (pO1 μ[A] (y k)) = y k := fun k ↦ (hax (y k)).2.2.1
  have f2 : ∀ k, pO1 a₁ (pO1 (snd A A) (y k)) = 0 := fun k ↦ (hax (y k)).2.1
  simp only [f1, f2, smul_zero, Finset.sum_const_zero] at this
  exact this

theorem exists_obRel_abelian : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ x : HO1 A.hom, ∃ (m : ℕ) (u v : Fin m → GlobForm A.hom),
      ObRel (OAff A.hom) x u v := by
  intro R _ A _ g hA hs x
  obtain ⟨hF, hC, -, -⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hs
  obtain ⟨n, y, w, hx⟩ := _root_.GlobalTheory.AbCoh.dRel_of_frame_exists R _ (OAff A.hom) hF x
  exact _root_.GlobalTheory.AbCoh.exists_obRel_of_dRel R _ (OAff A.hom) hF hC x n y w hx
    (fun l ↦ sum_dRel_eq_zero R A g hA hs x y w hx l)

end GlobalTheory.AbCoh
end

