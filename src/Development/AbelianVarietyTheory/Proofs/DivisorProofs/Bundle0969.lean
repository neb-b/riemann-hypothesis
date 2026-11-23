module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters
section
open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun GlobalTheory.SplitWeil

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

def toFun {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) :
    IndSp (points (Fin n)) ((ofChar (torusChar χ)).comp (leviTorus (w.adicCompletion E) (Fin n)).symm.toMonoidHom)
      →ₗ[ℂ] (GL (Fin n) (w.adicCompletion E) → ℂ) where
  toFun f := f.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toFun_injective {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) : Function.Injective (toFun w χ) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem toFun_intertwines {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (g) (f) :
    toFun w χ (prinSeries χ g f) = rightReg ℂ _ ℂ g (toFun w χ f) := rfl

theorem hasSatGL_prinSeries {n : ℕ} (α : Fin n → ℂˣ) :
    HasSatGL w (prinSeries fun i => unrChar (w.adicCompletion E) (α i)) (Finset.univ.val.map α) := by
  have hK : KO (w.adicCompletion E) (Fin n) = KGL w (n := n) := SphCompletion.KO_completion w n
  constructor
  · obtain ⟨φ, h, h1, -⟩ := Formalism.UG.Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
    obtain ⟨f, hf, rfl⟩ := (SphCompletion.isSpherical_iff E w n α _).1 h
    refine (Submodule.ne_bot_iff _).2 ⟨f, hK ▸ hf, fun h0 => ?_⟩
    subst h0
    simp at h1
  · intro x hx h0
    have hx' : x ∈ fixed (prinSeries fun i => unrChar (w.adicCompletion E) (α i)) (KO (w.adicCompletion E) (Fin n)) :=
      hK ▸ hx
    have hs := (SphCompletion.isSpherical_iff E w n α x.1.1).2 ⟨x, hx', rfl⟩
    exact IsSatVecGL.of_map (toFun w _) (toFun_intertwines w _) (toFun_injective w _)
      (isSatVecGL_of_isSpherical hs fun h => h0 (toFun_injective w _ (h.trans (map_zero _).symm)))

end GlobalTheory.PrinSat

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_parab_one (g : GL (Fin 1) k) : g ∈ parab k (points (Fin 1)) :=
  mem_parab_iff.2 fun a b _ _ hab => absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl _)

theorem cB_one (μ : kˣ →* ℂˣ) (p : parab k (points (Fin 1))) :
    PrinProd.cB (fun _ : Fin 1 => μ) p = μ (Matrix.GeneralLinearGroup.det (p : GL (Fin 1) k)) := by
  rw [PrinProd.cB_eq, Fin.prod_univ_one, Fin.prod_univ_one]
  have h : PrinProd.dg p 0 = Matrix.GeneralLinearGroup.det (p : GL (Fin 1) k) := by
    ext
    rw [PrinProd.val_dg, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    rfl
  rw [h]
  simp

def oneEquiv (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) :
    (detRep (Fin 1) μ).Equiv (prinSeries fun _ : Fin 1 => μ) := by
  let Ψ : ℂ →ₗ[ℂ] IndSp (points (Fin 1))
      ((ofChar (torusChar fun _ : Fin 1 => μ)).comp (leviTorus k (Fin 1)).symm.toMonoidHom) :=
    { toFun := fun c => ⟨⟨fun g => (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * c, fun p g => by
          show _ = PrinProd.sB (fun _ : Fin 1 => μ) p _
          rw [PrinProd.sB_apply, cB_one]
          beta_reduce
          rw [map_mul, map_mul, Units.val_mul, mul_assoc]⟩,
        MultiIrr.mem_smooth_of_eventually _ (Filter.mem_of_superset
          (IsOpen.mem_nhds (hμ.detChar (n := Fin 1)) (one_mem _)) fun u hu x => by
            have hu' : detChar (Fin 1) μ u = 1 := hu
            show (μ (Matrix.GeneralLinearGroup.det (x * u)) : ℂ) * c = (μ (Matrix.GeneralLinearGroup.det x) : ℂ) * c
            rw [map_mul (Matrix.GeneralLinearGroup.det), map_mul, ← detChar_apply (n := Fin 1) μ u, hu', mul_one])⟩
      map_add' := fun c d => Subtype.ext (Subtype.ext (funext fun g => mul_add _ _ _))
      map_smul' := fun c d => Subtype.ext (Subtype.ext (funext fun g => mul_left_comm _ _ _)) }
  refine Representation.Equiv.mk' ⟨Ψ, fun g => LinearMap.ext fun c => Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    (fun F => F.1.1 1) (fun c => ?_) (fun F => Subtype.ext (Subtype.ext (funext fun g => ?_)))
  · show (μ (Matrix.GeneralLinearGroup.det x) : ℂ) * (detRep (Fin 1) μ g c) =
      (μ (Matrix.GeneralLinearGroup.det (x * g)) : ℂ) * c
    simp [detRep, ofChar_apply, mul_assoc]
  · show (μ (Matrix.GeneralLinearGroup.det (1 : GL (Fin 1) k)) : ℂ) * c = c
    simp
  · show (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * F.1.1 1 = F.1.1 g
    have h := parInd_law (points (Fin 1)) _ F ⟨g, mem_parab_one g⟩ 1
    rw [mul_one] at h
    rw [h]
    change _ = PrinProd.sB (fun _ : Fin 1 => μ) ⟨g, mem_parab_one g⟩ _
    rw [PrinProd.sB_apply, cB_one]

end GlobalTheory.PrinSat

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun GlobalTheory.SplitWeil

theorem hasSatGL_of_equiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}
    {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (e : ρ.Equiv σ) {B : Multiset ℂˣ} (h : HasSatGL w σ B) : HasSatGL w ρ B := by
  let f : V →ₗ[ℂ] W := e.toLinearEquiv.toLinearMap
  have hi : ∀ g y, f (ρ g y) = σ g (f y) := fun g y => e.toIntertwiningMap.isIntertwining _ _ g y
  have inj : Function.Injective f := e.toLinearEquiv.injective
  constructor
  · obtain ⟨y, hy⟩ := h.exists_vec
    have hfy : f (e.toLinearEquiv.symm y) = y := e.toLinearEquiv.apply_symm_apply y
    have hs : IsSatVecGL w ρ (e.toLinearEquiv.symm y) B := IsSatVecGL.of_map f hi inj (by rw [hfy]; exact hy)
    exact (Submodule.ne_bot_iff _).2 ⟨_, hs.2.1, hs.1⟩
  · intro x hx h0
    have hfx : f x ∈ fixed σ (KGL w (n := n)) :=
      GlobalTheory.LGrp.mem_fixed.2 fun g hg => by rw [← hi, GlobalTheory.LGrp.mem_fixed.1 hx g hg]
    exact IsSatVecGL.of_map f hi inj (h.2 _ hfx fun h1 => h0 (inj (h1.trans (map_zero f).symm)))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_unrChar_of_ord {χ : kˣ →* ℂˣ} (h : IsUnram χ) {ϖ : kˣ} (hϖ : ord k ϖ = 1) :
    χ = unrChar k (χ ϖ) := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  refine MonoidHom.ext fun x => ?_
  have h1 : o (x / ϖ ^ ord k x) = 1 := by
    rw [map_div, map_zpow, show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd hϖ, ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    exact div_self' _
  have h2 := h _ (ord_eq_zero_iff.1 (ofAdd_eq_one.1 h1))
  rw [map_div, map_zpow, div_eq_one] at h2
  exact h2

theorem ord_unif {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    ord (w.adicCompletion E) (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)) = 1 := by
  have h : Valued.v ((Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  rw [SphCompletion.ord_completion, h, WithZero.log_exp, neg_neg]

end GlobalTheory.PrinSat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullLiftOneEqZero
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem AddCls.pull_lift_one_eq_zero {T : Over S} {c : Pic (A ⊗ T).left} (h : AddCls A c) {Y : Over S} (t : Y ⟶ T) :
    CechPic.pull (lift (1 : Y ⟶ A) t).left c = 0 := by
  have h1 := h Y 1 1 t
  rw [_root_.mul_one] at h1
  exact left_eq_add.1 h1

theorem AddCls.pull_eq_zero_of_unit {T Z : Over S} (z : Z ⟶ T) {c : Pic (A ⊗ Z).left} (h : AddCls A c)
    {T' : Scheme.{0}} (t : T' ⟶ (A ⊗ Z).left) (s : T' ⟶ T.left)
    (hts : t ≫ (A ◁ z).left = s ≫ (lift (1 : T ⟶ A) (𝟙 T)).left) : CechPic.pull t c = 0 := by
  let Y : Over S := Over.mk (t ≫ (A ⊗ Z).hom)
  let t' : Y ⟶ A ⊗ Z := Over.homMk t rfl
  have hs : s ≫ T.hom = t ≫ (A ⊗ Z).hom := by
    rw [← Over.w (A ◁ z), ← Category.assoc, hts, Category.assoc, Over.w]
  let s' : Y ⟶ T := Over.homMk s hs
  have h1 : t' ≫ A ◁ z = s' ≫ lift (1 : T ⟶ A) (𝟙 T) := Over.OverMorphism.ext hts
  have h2 : t' ≫ fst A Z = 1 := by
    have h3 := congrArg (· ≫ fst A T) h1
    simpa only [Category.assoc, whiskerLeft_fst, lift_fst, MonObj.comp_one] using h3
  have h4 : t' = lift (1 : Y ⟶ A) (t' ≫ snd A Z) := by
    rw [← h2, lift_comp_fst_snd]
  have h5 := h.pull_lift_one_eq_zero (t' ≫ snd A Z)
  rw [← h4] at h5
  exact h5

theorem pull_eq_of_compat {T Z Z' : Over S} (z : Z ⟶ T) (z' : Z' ⟶ T) (y : (addF A).obj (op Z))
    (y' : (addF A).obj (op Z'))
    (h : ∀ (Y : Over S) (a : Y ⟶ Z) (b : Y ⟶ Z'), a ≫ z = b ≫ z' → (addF A).map a.op y = (addF A).map b.op y')
    {T' : Scheme.{0}} (a : T' ⟶ (A ⊗ Z).left) (b : T' ⟶ (A ⊗ Z').left)
    (hab : a ≫ (A ◁ z).left = b ≫ (A ◁ z').left) : CechPic.pull a y.1 = CechPic.pull b y'.1 := by
  let Y : Over S := Over.mk (a ≫ (A ⊗ Z).hom)
  let a' : Y ⟶ A ⊗ Z := Over.homMk a rfl
  have hb : b ≫ (A ⊗ Z').hom = a ≫ (A ⊗ Z).hom := by
    rw [← Over.w (A ◁ z), ← Over.w (A ◁ z'), ← Category.assoc, ← hab, Category.assoc]
  let b' : Y ⟶ A ⊗ Z' := Over.homMk b hb
  have h1 : a' ≫ A ◁ z = b' ≫ A ◁ z' := Over.OverMorphism.ext hab
  have h2 : a' ≫ fst A Z = b' ≫ fst A Z' := by
    have h3 := congrArg (· ≫ fst A T) h1
    simpa only [Category.assoc, whiskerLeft_fst] using h3
  have h3 : (a' ≫ snd A Z) ≫ z = (b' ≫ snd A Z') ≫ z' := by
    have h3 := congrArg (· ≫ snd A T) h1
    simpa only [Category.assoc, whiskerLeft_snd] using h3
  have h4 := congrArg Subtype.val (h Y _ _ h3)
  rw [addF_map_val, addF_map_val] at h4
  have ha' : a' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (a' ≫ snd A Z) := by
    rw [lift_whiskerLeft, Category.id_comp, lift_comp_fst_snd]
  have hb' : b' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (b' ≫ snd A Z') := by
    rw [lift_whiskerLeft, Category.id_comp, h2, lift_comp_fst_snd]
  have h5 := congrArg (CechPic.pull (lift (a' ≫ fst A Z) (𝟙 Y)).left) h4
  rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, ← ha', ← hb'] at h5
  exact h5

theorem addF_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → (∀ (T : Over S) (J : Type) (Z : J → Over S) (z : ∀ i, Z i ⟶ T) (y : ∀ i, (addF A).obj (op (Z i))), (∀ i, IsOpenImmersion (z i).left) → (∀ p : T.left, ∃ i, p ∈ Set.range (z i).left) → (∀ (i k : J) (Y : Over S) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → (addF A).map a.op (y i) = (addF A).map b.op (y k)) → ∃ y₀ : (addF A).obj (op T), ∀ i, (addF A).map (z i).op y₀ = y i) := by
  intro S A _ hA T J Z z y hz hcov hc
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 T.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  obtain ⟨c₀, h0, hc₀⟩ := GlobalTheory.T.exists_glue_rigidified_line_bundle_classes (A ⊗ T).left T.left (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left he
    (_root_.GlobalTheory.PicGlue.fnBij_snd S A T hA) J (fun i ↦ (A ⊗ Z i).left) (fun i ↦ (A ◁ z i).left)
    (fun i ↦ haveI := hz i; (z i).left.opensRange) (fun i ↦ (y i).1)
    (fun i ↦ (GlobalTheory.whiskerLeft_isOpenImmersion_range S A T (Z i) (z i) (hz i)).1)
    (fun i x ↦ (GlobalTheory.whiskerLeft_isOpenImmersion_range S A T (Z i) (z i) (hz i)).2 x)
    (fun p ↦ hcov p)
    (fun i T' t s hts ↦ AddCls.pull_eq_zero_of_unit (z i) (y i).2 t s hts)
    (fun i k T' a b hab ↦ pull_eq_of_compat (z i) (z k) (y i) (y k) (hc i k) a b hab)
  refine ⟨⟨c₀, _root_.GlobalTheory.PicGlue.addCls_of_locally S A T hA c₀ h0 fun p ↦ ?_⟩, fun i ↦ Subtype.ext (hc₀ i)⟩
  obtain ⟨i, hi⟩ := hcov p
  refine ⟨Z i, z i, hz i, hi, ?_⟩
  rw [hc₀ i]
  exact (y i).2

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointLeSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.AdjSpanLift

open GlobalTheory.AdjBlock

section Linear

variable {K V H E : Type} [Field K] [AddCommGroup V] [Module K V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}

theorem range_adjoint_le_span [FiniteDimensional ℂ H] [FiniteDimensional ℂ E]
    (hli : LinearIndependent ℂ fun i => j (b i))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {e : Module.End K V}
    (he : ∀ v w, inner ℂ (j (e v)) (j w) = inner ℂ (j v) (j (e w))) {Θ : H →ₗ[ℂ] E}
    (hΘ : ∀ v, Θ (j (e v)) = Θ (j v)) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := by
  obtain ⟨U, hU⟩ := exists_cx hli hsp e
  have h1 : Θ ∘ₗ U = Θ := ext_of_span hsp fun v => by simp only [LinearMap.comp_apply, hU, hΘ]
  have h2 : ∀ w y, inner ℂ (U y) (j w) = inner ℂ y (U (j w)) := fun w y => by
    have : innerₛₗ ℂ (j w) ∘ₗ U = innerₛₗ ℂ (U (j w)) := ext_of_span hsp fun v => by
      simp only [LinearMap.comp_apply, innerₛₗ_apply_apply, hU, he]
    have h := LinearMap.congr_fun this y
    simp only [LinearMap.comp_apply, innerₛₗ_apply_apply] at h
    rw [← inner_conj_symm, h, inner_conj_symm]
  have h3 : ∀ y, U y ∈ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := fun y => by
    have hy : y ∈ Submodule.span ℂ (Set.range j) := hsp ▸ Submodule.mem_top
    refine (Submodule.span_le (p := (Submodule.span ℂ (j '' (LinearMap.range e : Set V))).comap U)).2 ?_ hy
    rintro _ ⟨v, rfl⟩
    show U (j v) ∈ Submodule.span ℂ (j '' (LinearMap.range e : Set V))
    rw [hU]
    exact Submodule.subset_span ⟨e v, ⟨v, rfl⟩, rfl⟩
  rintro _ ⟨u, rfl⟩
  have h4 : innerₛₗ ℂ (U (LinearMap.adjoint Θ u)) = innerₛₗ ℂ (LinearMap.adjoint Θ u) := ext_of_span hsp fun w => by
    simp only [innerₛₗ_apply_apply]
    rw [h2, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, hU, hΘ]
  rw [← (ext_inner_right ℂ fun w => LinearMap.congr_fun h4 w : U (LinearMap.adjoint Θ u) = LinearMap.adjoint Θ u)]
  exact h3 _

end Linear

section Pres

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [Field K] [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
  (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) {j : S.Forms →ₛₗ[σ] M.H}
  (hj : ∀ x, M.e (j x) = P.extL x)

include hM hj

theorem model_good_span {G0 E : Type} [Group G0] [Fintype G0] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {r : Representation K G0 S.Forms} (hr : S.ActGood r) {X : Finset (G0 → K)}
    (hX : ∀ c ∈ X, IsAbsIrrChar c) {Θ : M.H →ₗ[ℂ] E} (gE : Representation ℂ G0 E)
    (hΘ : ∀ g v, Θ (j (r g v)) = gE g (Θ (j v)))
    (he : ∀ y, ∑ g, σ ((idemOf X).coeff g) • gE g (Θ y) = Θ y) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ
      (j '' (LinearMap.range (S.gaOp r (goodAt X (⊥ : Subgroup G0) 1)) : Set S.Forms)) := by
  obtain ⟨h1, h2, h3⟩ := model_form P M hM hj
  rw [goodAt, level_idempotent_bot, mul_one]
  refine range_adjoint_le_span h1 h2 (sum_selfAdj r _ (fun g => ?_) fun g v w => ?_) fun v => ?_
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [coeff_idemOf, map_sum, map_mul, map_div₀, map_natCast, inv_inv]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [← (hX c hc).map_inv σ, ← (hX c hc).map_inv σ, inv_one, inv_inv]
  · rw [h3, h3, hr.unitary]
  · rw [← he (j v)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hΘ, RingHom.id_apply]

end Pres

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem proj_lifts_core {R : RealDat D A Ks} {F : Face D A} {s : ℕ} (hC : Core R F) (hOk : A.fam.Ok s) (i : Fin D.R.m) (t : T)
    (y : (R.HV i t).H) :
    ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gW i (sg0 D A) g (R.thG i t y) = R.thG i t y := by
  have h1 : R.thF i t y ∈ LinearMap.range (R.HW i (sg0 D A)).e :=
    (hC.models.HW i (sg0 D A)).2.1.ge (hC.thP.thF_mem i t y)
  obtain ⟨z, hz⟩ := h1
  have hs : ∀ a, sg0 D A a = D.what₂.embLL a := fun a => by rw [sg0, sgAt_mk _ R.hv0]
  have h2 : R.thG i t y = ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gW i (sg0 D A) g z := by
    refine (hC.models.HW i _).1 ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hC.thP.thG, ← hz, map_sum]
    refine (postOn_gaL (R.MW i (sg0 D A)) (R.βW i) (R.datWp i R.triv) R.eG _ _).trans ?_
    exact Finset.sum_congr rfl fun g _ => by rw [map_smul, hC.models.gW, RealDat.eC, hs]; rfl
  rw [h2]
  exact idem_idem _ hOk.irr _ z

theorem range_adjoint_lift_le (R : RealDat D A Ks) (F : Face D A) {s : ℕ} (hOk : A.fam.Ok s) (hC : Core R F)
    (hG : ∀ i t g (v : (A.MtCSD i t).Forms),
      R.thG i t (R.jV i t (A.leftGroupActionLift i t g v)) = R.gW i (sg0 D A) g (R.thG i t (R.jV i t v))) (i : Fin D.R.m) (t : T) :
    LinearMap.range (LinearMap.adjoint (R.thG i t)) ≤
      Submodule.span ℂ (R.jV i t '' ((A.fam.L i t).goodF A.X : Set (A.fam.L i t).S.Forms)) :=
  model_good_span (W := (R.cV i).W) (ι := Bridge.ratF (Vc D i)) (ρ := (R.cV i).coef.ρ)
    (J := (levEnv _ (R.βV i) (R.datVt i t)).J) (χ := (levEnv _ (R.βV i) (R.datVt i t)).χ) (R.B.L i t).pres (R.HV i t)
    (hC.models.HV i t) (hC.models.jV i t) (hOk.lifts i t).act hOk.irr
    (R.gW i (sg0 D A)) (hG i t) fun y => proj_lifts_core hC hOk i t y

end GlobalTheory.AdjSpanLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointThLeSpanGood
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.AdjGood

open GlobalTheory.AdjBlock

theorem range_adjoint_le_span {K V H E : Type} [Field K] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}
    [FiniteDimensional ℂ H] [FiniteDimensional ℂ E] (hli : LinearIndependent ℂ fun i => j (b i))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {e : Module.End K V}
    (he : ∀ v w, inner ℂ (j (e v)) (j w) = inner ℂ (j v) (j (e w))) {Θ : H →ₗ[ℂ] E}
    (hΘ : ∀ v, Θ (j (e v)) = Θ (j v)) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := by
  obtain ⟨U, hU⟩ := exists_cx hli hsp e
  have h1 : Θ ∘ₗ U = Θ := ext_of_span hsp fun v => by rw [LinearMap.comp_apply, hU, hΘ]
  have h2 : ∀ v y, inner ℂ (j (e v)) y = inner ℂ (j v) (U y) := fun v y => by
    have : innerₛₗ ℂ (j (e v)) = innerₛₗ ℂ (j v) ∘ₗ U := ext_of_span hsp fun w => by
      simp only [LinearMap.comp_apply, innerₛₗ_apply_apply, hU, he]
    exact LinearMap.congr_fun this y
  have h3 : LinearMap.adjoint U = U := ext_of_span hsp fun v => by
    refine ext_inner_right ℂ fun y => ?_
    rw [LinearMap.adjoint_inner_left, hU, h2]
  have h4 : LinearMap.range U ≤ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := by
    rw [LinearMap.range_eq_map, ← hsp, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    rw [hU]
    exact Submodule.subset_span ⟨e v, ⟨v, rfl⟩, rfl⟩
  refine le_trans ?_ h4
  rw [← h1, LinearMap.adjoint_comp, h3]
  exact LinearMap.range_comp_le_range _ _

theorem model_good_span {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
    {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) {j : S.Forms →ₛₗ[σ] M.H}
    (hj : ∀ x, M.e (j x) = P.extL x)
    {G0 E : Type} [Group G0] [Fintype G0] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {r : Representation K G0 S.Forms} (hr : S.ActGood r) {X : Finset (G0 → K)}
    (hX : ∀ c ∈ X, IsAbsIrrChar c) {Θ : M.H →ₗ[ℂ] E} (gE : Representation ℂ G0 E)
    (hΘ : ∀ g v, Θ (j (r g v)) = gE g (Θ (j v)))
    (he : ∀ y, ∑ g, σ ((idemOf X).coeff g) • gE g (Θ y) = Θ y) :
    LinearMap.range (LinearMap.adjoint Θ) ≤
      Submodule.span ℂ (j '' (LinearMap.range (S.gaOp r (goodAt X (⊥ : Subgroup G0) 1)) : Set S.Forms)) := by
  obtain ⟨h1, h2, h3⟩ := model_form P M hM hj
  rw [goodAt, level_idempotent_bot, mul_one]
  refine range_adjoint_le_span h1 h2 (sum_selfAdj r _ (fun g => ?_) fun g v w => ?_) fun v => ?_
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [coeff_idemOf, map_sum, map_mul, map_div₀, map_natCast, inv_inv]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [← (hX c hc).map_inv σ, ← (hX c hc).map_inv σ, inv_one, inv_inv]
  · rw [h3, h3, hr.unitary]
  · rw [← he (j v)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hΘ, RingHom.id_apply]

theorem proj_rows_core {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (hC : Core R F) (y : R.HE.H) : ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gE g y = y := by
  refine hC.models.HE.1 ?_
  have h1 : R.HE.e y ∈ R.EEat R.triv := by
    rw [← hC.models.HE.2.1]
    exact LinearMap.mem_range_self _ y
  have h2 : postOn (R.MY 0) R.e0 (R.HE.e y) - R.HE.e y = 0 := h1.2
  refine Eq.trans ?_ ((postOn_gaL (R.MY 0) (R.βY 0) (R.dat0 R.triv) R.eG _ _).symm.trans (sub_eq_zero.1 h2))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, hC.models.gE]; rfl

theorem range_adjoint_Th_le_span_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ t g (v : (A.MtildeCSD t).Forms), R.Th t (R.jX t (A.leftGroupActionRight t g v)) = R.gE g (R.Th t (R.jX t v))) → ∀ t, LinearMap.range (LinearMap.adjoint (R.Th t)) ≤ Submodule.span ℂ (R.jX t '' ((A.fam.R t).goodF A.X : Set (A.fam.R t).S.Forms)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hG t
  exact model_good_span (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ) (J := (levEnv _ R.βX (R.datXt t)).J)
    (χ := (levEnv _ R.βX (R.datXt t)).χ) (R.B.R t).pres (R.HX t) (hC.models.HX t) (hC.models.jX t) (hOk.what₂ t).act hOk.irr
    R.gE (hG t) fun y => proj_rows_core hC _

end GlobalTheory.AdjGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelOfConjInGroupOfCommonFormStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rel_of_conj_in_group_of_common_form : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' g : G.Cˣ) (s s' sg : ℚ), 0 < s → 0 < s' → 0 < sg → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y') → (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B → g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' → P.Rel P' := by
  first | (exact @GlobalTheory.RelConj.rel_of_conj_in_form) | (exact GlobalTheory.RelConj.rel_of_conj_in_form) | (intros; apply GlobalTheory.RelConj.rel_of_conj_in_form  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInverseGramLocalBasisIntegralStatement
section
open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_inverseGram_localBasis_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (w : HeightOneSpectrum (𝓞 E)), (∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J y x))) → ∀ (X : Matrix (Fin n) (Fin n) E), IsUnit X.det → IsUnit (Xᵀ * J * X.map σ).det → (∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1) → ∀ (s : 𝓞 E), s ∉ w.asIdeal → (∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r) → ∀ (e : E), (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) → ∀ i k, w.valuation E (e * (Xᵀ * J * X.map σ)⁻¹ i k) ≤ 1 := by
  first | exact @GlobalTheory.selfDual_inv_gram_integral | exact GlobalTheory.selfDual_inv_gram_integral | (intros; apply GlobalTheory.selfDual_inv_gram_integral <;> assumption)
end

