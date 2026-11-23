module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepDualPairing
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.FrameAut.VecProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {S : Type} [AddCommGroup S] [Module ℂ S]

def forms (ρ : Representation ℂ (infU E n) S) : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {f | (∀ v, f v ∈ autU E n) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)}
  add_mem' ha hb := ⟨fun v => add_mem (ha.1 v) (hb.1 v), fun x v => by
    rw [LinearMap.add_apply, LinearMap.add_apply, ha.2, hb.2, map_add (f := _)]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ ha := ⟨fun v => Submodule.smul_mem _ c (ha.1 v), fun x v => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ha.2, map_smul]⟩


variable (E n S) in
def post : Representation ℂ (finU (E := E) (n := n)) (S →ₗ[ℂ] (UA E n → ℂ)) where
  toFun k := LinearMap.llcomp ℂ _ _ _ (RU E n k)
  map_one' := LinearMap.ext fun f => LinearMap.ext fun v => funext fun g => congrArg (f v) (mul_one g)
  map_mul' a b := LinearMap.ext fun f => LinearMap.ext fun v => funext fun g => congrArg (f v) (mul_assoc g a b).symm

@[simp] theorem post_apply (k : finU (E := E) (n := n)) (f : S →ₗ[ℂ] (UA E n → ℂ)) (v : S) :
    post E n S k f v = RU E n k (f v) := rfl

theorem post_mem (ρ : Representation ℂ (infU E n) S) (k : finU (E := E) (n := n)) (f : S →ₗ[ℂ] (UA E n → ℂ))
    (h : f ∈ forms ρ) : post E n S k f ∈ forms ρ :=
  ⟨fun v => RU_mem_autU _ _ (h.1 v), fun x v => by
    rw [post_apply, post_apply, h.2, RU_RU, RU_RU, fin_mul_inf k.2 x.2]⟩

def rep (ρ : Representation ℂ (infU E n) S) : Representation ℂ (finU (E := E) (n := n)) (forms ρ) :=
  GlobalTheory.PRep.sub (post E n S) (forms ρ) (post_mem ρ)

end GlobalTheory.FrameAut.VecProj

namespace GlobalTheory.FrameAut.VecProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {S : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]

def ev (ρ : Representation ℂ (infU E n) S) (v : S) : forms ρ →ₗ[ℂ] autU E n where
  toFun f := ⟨f.1 v, f.2.1 v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def form (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (ρ : Representation ℂ (infU E n) S) :
    forms ρ →ₗ⋆[ℂ] forms ρ →ₗ[ℂ] ℂ :=
  ∑ i, (B.comp (ev ρ (Module.finBasis ℂ S i))).compl₂ (ev ρ (Module.finBasis ℂ S i))

theorem form_apply (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (ρ : Representation ℂ (infU E n) S) (f g : forms ρ) :
    form B ρ f g = ∑ i, B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) g) := by
  simp [form, LinearMap.sum_apply]

end GlobalTheory.FrameAut.VecProj

namespace GlobalTheory.FrameAut.VecProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {S : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]

theorem form_herm (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u)
    (ρ : Representation ℂ (infU E n) S) (f g : forms ρ) : star (form B ρ f g) = form B ρ g f := by
  rw [form_apply, form_apply, star_sum]
  exact Finset.sum_congr rfl fun i _ => hh _ _

theorem form_nonneg (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hp : ∀ v, 0 ≤ (B v v).re)
    (ρ : Representation ℂ (infU E n) S) (f : forms ρ) : 0 ≤ (form B ρ f f).re := by
  rw [form_apply, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => hp _

theorem form_def (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u)
    (hp : ∀ v, 0 ≤ (B v v).re) (hd : ∀ v, B v v = 0 → v = 0)
    (ρ : Representation ℂ (infU E n) S) (f : forms ρ) (h0 : form B ρ f f = 0) : f = 0 := by
  rw [form_apply] at h0
  have hre : ∑ i, (B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f)).re = 0 := by
    rw [← Complex.re_sum, h0, Complex.zero_re]
  have hz : ∀ i, B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f) = 0 := by
    intro i
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp _)).1 hre i (Finset.mem_univ i)
    have h2 : (B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f)).im = 0 := by
      have := congrArg Complex.im (hh (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f))
      rw [Complex.star_def, Complex.conj_im] at this
      linarith
    exact Complex.ext h1 h2
  apply Subtype.ext
  refine (Module.finBasis ℂ S).ext fun i => ?_
  have := congrArg Subtype.val (hd _ (hz i))
  simpa [ev] using this

theorem form_inv (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ)
    (hi : ∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v)
    (ρ : Representation ℂ (infU E n) S) (k : finU (E := E) (n := n)) (f g : forms ρ) :
    form B ρ (rep ρ k f) (rep ρ k g) = form B ρ f g := by
  rw [form_apply, form_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hi (k : UA E n) (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) g)

theorem rep_smooth (ρ : Representation ℂ (infU E n) S) (f : forms ρ) :
    IsOpen {k : finU (E := E) (n := n) | rep ρ k f = f} := by
  let b := Module.finBasis ℂ S
  convert isOpen_iInter_of_finite fun i => (f.2.1 (b i)).level using 1
  ext k
  rw [Set.mem_iInter]
  exact ⟨fun h i => LinearMap.congr_fun (congrArg Subtype.val h) (b i), fun h => Subtype.ext (b.ext h)⟩

theorem rep_fd (ρ : Representation ℂ (infU E n) S) (K : Subgroup (finU (E := E) (n := n))) (hK : IsOpen (K : Set (finU (E := E) (n := n)))) :
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed (rep ρ) K) := by
  have hM := GlobalTheory.T.finiteDimensional_vectorValued_definiteUnitaryForms E n S ρ K hK ((GlobalTheory.PRep.fixed (rep ρ) K).map (forms ρ).subtype) (by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨fun v γ hγ x => (g.2.1 v).left γ hγ x, g.2.2, fun k hk v => ?_⟩
    have h1 : rep ρ k g = g := by
      have := hg ⟨k, hk⟩
      rw [MonoidHom.one_apply, Units.val_one, one_smul] at this
      exact this
    exact LinearMap.congr_fun (congrArg Subtype.val h1) v)
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (forms ρ).injective_subtype _).symm

end GlobalTheory.FrameAut.VecProj

namespace GlobalTheory.FrameAut.VecProj

end GlobalTheory.FrameAut.VecProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactificationOpenOfClosed
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.FlatRow

theorem isOpen_closure_of_isOpen_components {Z : Type} [TopologicalSpace Z]
    (h : ∀ z : Z, IsOpen (irreducibleComponent z)) {W : Set Z} (hW : IsOpen W) : IsOpen (closure W) := by
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨irreducibleComponent z, ?_, h z, mem_irreducibleComponent⟩
  have hne : (irreducibleComponent z ∩ W).Nonempty := mem_closure_iff.1 hz _ (h z) mem_irreducibleComponent
  intro y hy
  refine mem_closure_iff.2 fun O hO hyO => ?_
  obtain ⟨a, -, ha⟩ := isIrreducible_irreducibleComponent.isPreirreducible O W hO hW ⟨y, hy, hyO⟩ hne
  exact ⟨a, ha⟩

theorem isOpen_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens), IsClosed (U : Set (Xo.XF c)) → IsOpen (FramedFlatCoordinates.compactification Y U) := by
  intro E _ _ _ H Dw l Xo c Y U _
  have i₀ : IsIso (spMap (RingHom.id c.F)) := by
    rw [show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _]; infer_instance
  have i₁ : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := inferInstance
  have hn : Geo.Tor.IsNormalScheme (FramedFlatCoordinates.genFibre Y) := fun x => by
    let e := (asIso ((pullback.fst Y.s (spMap (RingHom.id c.F))).stalkMap x)).commRingCatIsoToRingEquiv
    obtain ⟨h₁, h₂⟩ := Y.normal (pullback.fst Y.s (spMap (RingHom.id c.F)) x)
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsProper Y.s := by
    obtain ⟨N, i, hi, e⟩ := Y.proj
    have := isProper_str c.F N
    rw [← e]
    infer_instance
  have : IsLocallyNoetherian (FramedFlatCoordinates.genFibre Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (RingHom.id c.F)))
  have := Y.jQ_open
  exact isOpen_closure_of_isOpen_components
    (fun z => GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z))
    (Y.jQ.isOpenEmbedding.isOpenMap _ U.isOpen)

end GlobalTheory.FlatRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisBaseChangeLocalAlgebra
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.EigBasisLocal

open EigenSplit LieEigen
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD)

theorem eigenBasis_map {O R R' I : Type} [CommRing O] [CommRing R] [CommRing R'] [Finite I]
    {σ : I → O →+* R} (hσ : IsSplitting σ) {n m : ℕ} (ρ : O →+* Module.End R (Fin n → R)) (f : R →+* R')
    (ρ' : O →+* Module.End R' (Fin n → R')) (hf : ∀ a x, f ∘ ρ a x = ρ' a (f ∘ x)) (τ : I)
    (b : Fin m → Fin n → R) (hb : ∀ i, b i ∈ eigenSub ρ (σ τ))
    (H : ∀ c ∈ eigenSub ρ (σ τ), ∃! d : Fin m → R, ∑ i, d i • b i = c) :
    (∀ i, f ∘ b i ∈ eigenSub ρ' (f.comp (σ τ))) ∧
      ∀ c ∈ eigenSub ρ' (f.comp (σ τ)), ∃! d : Fin m → R', ∑ i, d i • (f ∘ b i) = c := by
  let _ := f.toAlgebra
  let F : (Fin n → R) →ₗ[R] (Fin n → R') := (Algebra.linearMap R R').compLeft (Fin n)
  have hF : IsBaseChange R' F := IsBaseChange.finitePow (Fin n) (IsBaseChange.linearMap R R')
  have hf' : ∀ a x, F (ρ a x) = ρ' a (F x) := hf
  have hB := isBaseChange_eigenMapAlgebra hσ hf' hF τ
  let b' : Fin m → eigenSub ρ (σ τ) := fun i => ⟨b i, hb i⟩
  have key : ∀ c : eigenSub ρ (σ τ), ∃! d, Fintype.linearCombination R b' d = c := fun c => by
    refine (existsUnique_congr fun d => ?_).1 (H _ c.2)
    rw [Subtype.ext_iff, Fintype.linearCombination_apply]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    rfl
  let B : Module.Basis (Fin m) R (eigenSub ρ (σ τ)) :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ ((Function.bijective_iff_existsUnique _).2 key)).symm
  have hBi : ∀ i, (B i : Fin n → R) = b i := fun i => by
    simp [B, b', Module.Basis.coe_ofEquivFun, Fintype.linearCombination_apply_single]
  let B' := hB.basis B
  have hB' : ∀ i, (B' i : Fin n → R') = f ∘ b i := fun i => by
    rw [← hBi, IsBaseChange.basis_apply]
    rfl
  refine ⟨fun i => hB' i ▸ (B' i).2, fun c hc => ?_⟩
  have k : ∀ d : Fin m → R', ∑ i, d i • (f ∘ b i) = c ↔ B'.equivFun ⟨c, hc⟩ = d := fun d => by
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff, eq_comm]
    simp [hB']
  simp only [k]
  exact existsUnique_eq'

theorem isEigBasis_iff {O R : Type} [CommRing O] [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {n m : ℕ} {e : Fin n → (epsR R ⟶ G)} (he : IsLieBasis e) {act : OAct O G}
    {ρ : O →+* Module.End R (Fin n → R)} (hρ : ∀ a c, prodPts (ρ a c) e = prodPts c e ≫ act.act a)
    (χ : O →+* R) (b : Fin m → Fin n → R) :
    EigenvectorLieDegree.IsEigBasis act χ (fun i => prodPts (b i) e) ↔ (∀ i, b i ∈ eigenSub ρ χ) ∧
      ∀ c ∈ eigenSub ρ χ, ∃! d : Fin m → R, ∑ i, d i • b i = c := by
  have mem : ∀ c, EigenvectorLieDegree.IsEigVec act χ (prodPts c e) ↔ c ∈ eigenSub ρ χ := fun c => by
    rw [mem_eigenSub]
    refine (and_iff_right (isTangent_prodPts he.1 c)).trans (forall_congr' fun a => ?_)
    rw [← hρ, ← (prodPts_injective he).eq_iff]
    rw [prodPts_smul, Over.OverMorphism.ext_iff]
    rfl
  have cb : ∀ d c, IsLieComb d (fun i => prodPts (b i) e) (prodPts c e) ↔ ∑ i, d i • b i = c := fun d c => by
    refine (Chart.isLieComb_iff d _ _).trans ?_
    rw [prodPts_prodPts he.1, eq_comm]
    exact (prodPts_injective he).eq_iff
  refine and_congr (forall_congr' fun i => mem _) ⟨fun h c hc => ?_, fun h w hw => ?_⟩
  · exact (existsUnique_congr fun d => cb d c).1 (h _ ((mem c).2 hc))
  · obtain ⟨c, rfl⟩ := exists_prodPts he hw.1
    exact (existsUnique_congr fun d => cb d c).2 (h _ ((mem c).1 hw))

theorem isEigBasis_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (l : Level H) (c : Coeff l) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] (j : c.F →+* R) (g : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (n : SABMap t' t (spMap g)) (τ : E →+* ℂ) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR R' ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act (FramedFlatCoordinates.chr c τ j) v → (∀ i, IsVecOver g n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act (FramedFlatCoordinates.chr c τ (g.comp j)) v' := by
  classical
  intro E _ _ _ H l c R R' _ _ _ j g t t' n τ m v v' hv hv'
  let σ₀ : (E →+* ℂ) → 𝓞 E →+* c.F := fun τ =>
    (τ.codRestrict c.F.toSubfield (c.conj τ)).comp (algebraMap (𝓞 E) E)
  have hσ₀ : Function.Injective σ₀ := fun τ τ' h =>
    (isSplitting_complex E).injective
      (RingHom.ext fun a => congrArg Subtype.val (RingHom.congr_fun h a))
  have hσ : IsSplitting fun τ => j.comp (σ₀ τ) :=
    isSplitting_of_isDomain hσ₀ (NumberField.Embeddings.card E ℂ) j (by
      simpa using (isUnit_discr_of_charZero (E := E) c.F).map j)
  obtain ⟨N, e, he⟩ := Chart.exists_isLieBasis t.G t.semi.smooth
  obtain ⟨e', he', ee⟩ := exists_isLieBasis_baseChange R R' g _ _ _ n.cart t.semi.smooth N e he
  obtain ⟨ρ, hρ⟩ := exists_action he t.act
  obtain ⟨ρ', hρ'⟩ := exists_action he' t'.act
  choose b hb using fun i => exists_prodPts he (hv.1 i).1
  obtain rfl : v = fun i => prodPts (b i) e := (funext hb).symm
  obtain rfl : v' = fun i => prodPts (g ∘ b i) e' := funext fun i =>
    Over.OverMorphism.ext (n.cart.1.hom_ext ((hv' i).trans (prodPts_left n.cart ee _).symm)
      ((Over.w _).trans (Over.w _).symm))
  obtain ⟨h1, h2⟩ := (isEigBasis_iff he hρ _ b).1 hv
  exact (isEigBasis_iff he' hρ' _ _).2
    (eigenBasis_map hσ ρ g ρ' (action_baseChange n.cart he' ee n.act hρ hρ') τ b h1 h2)

end GlobalTheory.EigBasisLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisLocalizationAtPrime
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.EigBasisPrime

theorem eig_localization {R R' O L L' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (S : Submonoid R)
    [IsLocalization S R'] [CommRing O] [Module.Finite ℤ O] [AddCommGroup L] [Module R L] [Module O L]
    [SMulCommClass O R L] [AddCommGroup L'] [Module R' L'] [Module O L'] [SMulCommClass O R' L'] (f : L →+ L')
    (hs : ∀ (r : R) x, f (r • x) = algebraMap R R' r • f x) (ha : ∀ (a : O) x, f (a • x) = a • f x)
    (lift : ∀ y, ∃ q ∈ S, ∃ x, f x = algebraMap R R' q • y) (uniq : ∀ x, f x = 0 → ∃ q ∈ S, q • x = 0)
    (χ : O →+* R) {m : ℕ} (v : Fin m → L)
    (hv : ∀ w : L, (∀ a, a • w = χ a • w) → ∃! c : Fin m → R, w = ∑ i, c i • v i)
    (w : L') (hw : ∀ a, a • w = algebraMap R R' (χ a) • w) : ∃! c : Fin m → R', w = ∑ i, c i • f (v i) := by
  classical
  have unit : ∀ q ∈ S, IsUnit (algebraMap R R' q) := fun q hq => IsLocalization.map_units R' ⟨q, hq⟩
  have inj : ∀ d : Fin m → R', ∑ i, d i • f (v i) = 0 → d = 0 := fun d hd => by
    obtain ⟨⟨q, hq⟩, hqi⟩ := IsLocalization.exist_integer_multiples_of_finite S d
    choose d' hd' using hqi
    have h0 : f (∑ i, d' i • v i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, hs, hd', Algebra.smul_def, mul_smul]
      rw [← Finset.smul_sum, hd, smul_zero]
    obtain ⟨r, hr, h1⟩ := uniq _ h0
    have h2 : r • d' = 0 := (hv 0 (by simp)).unique
      (by rw [← h1, Finset.smul_sum]; simp [mul_smul]) (by simp)
    funext i
    have h3 := congrArg (algebraMap R R') (congrFun h2 i)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hd', Algebra.smul_def, Pi.zero_apply,
      map_zero] at h3
    exact (unit q hq).mul_right_eq_zero.1 ((unit r hr).mul_right_eq_zero.1 h3)
  obtain ⟨q, hq, x, hx⟩ := lift w
  have h1 : ∀ a : O, ∃ r ∈ S, r • (a • x - χ a • x) = 0 := fun a => uniq _ (by
    rw [map_sub, ha, hs, hx, smul_comm a, hw, smul_comm, sub_self])
  choose r hr h1 using h1
  obtain ⟨s, hsp⟩ := Module.Finite.fg_top (R := ℤ) (M := O)
  have hQ : ∏ a ∈ s, r a ∈ S := S.prod_mem fun a _ => hr a
  obtain ⟨c, hc, -⟩ := hv ((∏ a ∈ s, r a) • x) fun a => by
    have : a ∈ Submodule.span ℤ (s : Set O) := hsp ▸ Submodule.mem_top
    induction this using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem r (Finset.mem_coe.1 hb)
      rw [smul_comm b, smul_comm (χ b), ← sub_eq_zero, ← smul_sub, hk, _root_.mul_comm, mul_smul, h1, smul_zero]
    | zero => simp
    | add b b' _ _ e e' => rw [add_smul, e, e', map_add (f := _), add_smul]
    | smul k b _ e => rw [smul_assoc, e, map_zsmul, smul_assoc]
  have h2 := congrArg f hc
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hs, hx, smul_smul] at h2
  obtain ⟨u, hu⟩ := ((unit _ hQ).mul (unit q hq)).exists_left_inv
  have h3 : w = ∑ i, (u * algebraMap R R' (c i)) • f (v i) := by
    simp only [mul_smul u]
    rw [← Finset.smul_sum, ← h2, smul_smul, hu, one_smul]
  refine ⟨_, h3, fun c' hc' => sub_eq_zero.1 (inj _ ?_)⟩
  simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [← hc', ← h3, sub_self]

theorem isEigBasis_atPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] (t : SAB H (Sp R)) (t' : SAB H (Sp (Localization.AtPrime p))) (n : SABMap t' t (spMap (algebraMap R (Localization.AtPrime p)))) (χ : 𝓞 E →+* R) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR (Localization.AtPrime p) ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act χ v → (∀ i, IsVecOver (algebraMap R (Localization.AtPrime p)) n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act ((algebraMap R (Localization.AtPrime p)).comp χ) v' := by
  intro E _ _ _ H R _ p _ t t' n χ m v v' hv hv'
  have := t.semi.smooth
  have : ∀ s : R, Smooth (Chart.Gs t.G s).hom := fun s => show Smooth (pullback.snd t.G.hom _) from inferInstance
  let j := algebraMap R (Localization.AtPrime p)
  choose g hg hgu using fun x : epsR R ⟶ t.G => existsUnique_isVecOver (f := j) n.cart.1 x
  let f₀ : Serre.Lie t.act → Serre.Lie t'.act := fun x =>
    Serre.Lie.mk _ (g x.hom) ((hg _).isTangent n.cart x.isTangent)
  have hf : ∀ x y, f₀ x = y ↔ IsVecOver j n.φ x.hom y.hom := fun x y =>
    ⟨fun e => e ▸ hg _, fun e => Serre.Lie.ext (hgu _ _ e).symm⟩
  have comb : ∀ (k : ℕ) (c : Fin k → R) (x : Fin k → Serre.Lie t.act),
      f₀ (∑ i, c i • x i) = ∑ i, j (c i) • f₀ (x i) := fun k c x =>
    (hf _ _).2 ((lieComb_baseChange _ _ j t.G t'.G n.φ n.cart k (fun i => (x i).hom) _ c (fun i => (f₀ (x i)).hom) _
      (fun i => hg _) ((Serre.Lie.isLieComb_iff c x _).2 rfl)).2 ((Serre.Lie.isLieComb_iff _ _ _).2 rfl))
  let f : Serre.Lie t.act →+ Serre.Lie t'.act := AddMonoidHom.mk' f₀ fun x y => by
    simpa using comb 2 1 ![x, y]
  have hs : ∀ (r : R) x, f (r • x) = j r • f x := fun r x => by
    change f₀ _ = _ • f₀ _
    simpa using comb 1 ![r] ![x]
  have ha : ∀ (a : 𝓞 E) x, f (a • x) = a • f x := fun a x => (hf _ _).2 (by
    have := hg x.hom
    simp only [IsVecOver] at this ⊢
    change (g x.hom ≫ t'.act.act a).left ≫ _ = _ ≫ (x.hom ≫ t.act.act a).left
    rw [Over.comp_left, Category.assoc, n.act a, ← Category.assoc, this, Category.assoc, Over.comp_left])
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv n.cart (epsR (Localization.AtPrime p))
    (spMap (algebraMap R (DualNumber (Localization.AtPrime p)))) (spMap_comp_spMap _ _).symm
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv n.cart (𝟙_ (Over (Sp (Localization.AtPrime p)))) (spMap j)
    (Category.id_comp _).symm
  have one : (1 : Over.mk (spMap j) ⟶ t.G).left = η[t'.G].left ≫ n.φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have lift : ∀ y, ∃ q ∈ p.primeCompl, ∃ x, f x = j q • y := fun y => by
    obtain ⟨q, hq, w, hw, hwy⟩ := Chart.tan_prime_lift p (y' := e y.hom) (Over.OverMorphism.ext (by
      refine Eq.trans ?_ one.symm
      rw [Over.comp_left, he, ← y.isTangent]
      exact (Category.assoc _ _ _).symm))
    refine ⟨q, hq, Serre.Lie.mk _ w ((Chart.isTan_iff _).1 hw), (hf _ _).2 ?_⟩
    have := congrArg (fun z => z.left) hwy
    simp only [Over.comp_left, he] at this
    exact (Category.assoc _ _ _).trans this.symm
  have uniq : ∀ x, f x = 0 → ∃ q ∈ p.primeCompl, q • x = 0 := fun x hx => by
    obtain ⟨q, hq, h⟩ := Chart.tan_prime_uniq p (w := x.hom) ((Chart.isTan_iff _).2 x.isTangent)
      (Over.OverMorphism.ext (by
        rw [← map_one e, he]
        exact ((hf _ _).1 hx).symm))
    exact ⟨q, hq, Serre.Lie.ext h⟩
  let y : Fin m → Serre.Lie t.act := fun i => Serre.Lie.mk _ (v i) (hv.1 i).1
  have hy : v' = fun i => (f (y i)).hom := funext fun i => hgu _ _ (hv' i)
  subst hy
  refine ⟨fun i => ⟨Serre.Lie.isTangent _, Serre.Lie.mem_eig_iff_left.1 fun a => ?_⟩, fun w hw => ?_⟩
  · rw [← ha, (Serre.Lie.mem_eig_iff_left (v := y i)).2 (hv.1 i).2 a, hs]
    rfl
  · refine (existsUnique_congr fun c => ?_).1 (eig_localization p.primeCompl f hs ha lift uniq χ y
      (fun z hz => (existsUnique_congr fun c => ?_).1
        (hv.2 z.hom ⟨z.isTangent, (Serre.Lie.mem_eig_iff_left (τ := χ) (v := z)).1 hz⟩))
      (Serre.Lie.mk _ w hw.1) ((Serre.Lie.mem_eig_iff_left (τ := j.comp χ) (v := Serre.Lie.mk _ w hw.1)).2 hw.2))
    · rw [Serre.Lie.isLieComb_iff]
      exact ⟨fun h => congrArg Serre.Lie.hom h, fun h => Serre.Lie.ext h⟩
    · exact (Serre.Lie.isLieComb_iff c y _).trans ⟨fun h => Serre.Lie.ext h, fun h => congrArg Serre.Lie.hom h⟩

end GlobalTheory.EigBasisPrime
end
end

