module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitSupportedClassScalarMemValuationRing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralRankinSelbergThetaEqWhittakerUnfolding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.LanglandsMultisegmentsOfSeg
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsObjMapOfCoprime
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CoverExp

open GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

theorem exists_sabMap_types {D D₁ D₂ : Datum H}
    {l : Level H} {b : Base l ℂ} {s : Sp ℂ ⟶ Sp ℂ} (o₁ o₂ : Obj D l b s)
    {ty₁ ty₂ : Fin g → (E →+* ℂ)} {P₁ : D₁.La →+ (Fin g → ℂ)} {P₂ : D₂.La →+ (Fin g → ℂ)} (hP₁ : IsPeriod D₁ ty₁ P₁)
    (hP₂ : IsPeriod D₂ ty₂ P₂) {e₁ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₁.t.G)}
    {e₂ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₂.t.G)} (a₁ : ∀ z w, e₁ (z + w) = e₁ z * e₁ w)
    (s₁ : Function.Surjective e₁) (s₂ : Function.Surjective e₂)
    (r₁ : ReadsPeriods o₁.t unitOn D₁ ty₁ P₁ e₁) (r₂ : ReadsPeriods o₂.t unitOn D₂ ty₂ P₂ e₂)
    (u₁ : ∀ (g₀ : ℕ) (u : HolUnif o₁.t.G o₁.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₁ (h z) = u.ex z)
    (u₂ : ∀ (g₀ : ℕ) (u : HolUnif o₂.t.G o₂.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₂ (h z) = u.ex z)
    (gam : D₁.La ≃ₗ[𝓞 E] D₂.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hEF : ∀ a b, D₂.EF (gam a) (gam b) = D₁.EF a b) (hh : ∀ a, P₂ (gam a) = h (P₁ a)) :
    ∃ m : SABMap o₁.t o₂.t (𝟙 _), ∀ z, (e₁ z).left ≫ m.φ = (e₂ (h z)).left := by
  have hT := GlobalTheory.ArcCM.known_holds.theta
  have hL := GlobalTheory.ArcCM.known_holds.laws
  have hG := hL.globalFns
  have hA : HomAlg := GlobalTheory.exists_isMonHom_of_map_lattice hT hL
  have hD : WeilDet := _root_.GlobalTheory.lam_iso_of_weil_pairings hL
  have p₁ := GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₁
  have p₂ := GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₂
  obtain ⟨α, hα, hα'⟩ : ∃ α : o₁.t.G ⟶ o₂.t.G, IsMonHom α ∧ ∀ z, e₂ (h z) = e₁ z ≫ α :=
    exists_hom hT hA (objPol o₁ p₁) (objPol o₂ p₂) rfl u₁ u₂ h.toLinearMap fun z hz => by
      obtain ⟨a, rfl⟩ := (r₁.1 z).1 hz
      exact (r₂.1 _).2 ⟨gam a, hh a⟩
  obtain ⟨β, -, hβ'⟩ : ∃ β : o₂.t.G ⟶ o₁.t.G, IsMonHom β ∧ ∀ z, e₁ (h.symm z) = e₂ z ≫ β :=
    exists_hom hT hA (objPol o₂ p₂) (objPol o₁ p₁) rfl u₂ u₁ h.symm.toLinearMap fun z hz => by
      obtain ⟨a, rfl⟩ := (r₂.1 z).1 hz
      refine (r₁.1 _).2 ⟨gam.symm a, h.injective ?_⟩
      rw [← hh, gam.apply_symm_apply]
      exact (h.apply_symm_apply _).symm
  have := p₁.1.smooth
  have := p₂.1.smooth
  have := p₁.1.proper
  have := p₂.1.proper
  have : IsReduced o₁.t.G.left := isReduced_of_smooth_complex _ o₁.t.G.hom inferInstance
  have : IsReduced o₂.t.G.left := isReduced_of_smooth_complex _ o₂.t.G.hom inferInstance
  let ψ : o₁.t.G ≅ o₂.t.G :=
    { hom := α
      inv := β
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := s₁ x
        rw [← Category.assoc, ← hα', ← hβ', h.symm_apply_apply, Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := s₂ x
        rw [← Category.assoc, ← hβ', ← hα', h.apply_symm_apply, Category.comp_id] }
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty₁ k (a : E) * z k) = fun k => ty₂ k (a : E) * h z k := fun a z => by
    have k : (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty₁ k (a : E)) =
        LinearMap.mulLeft ℝ (fun k => ty₂ k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ) := by
      refine LinearMap.ext_on_range hP₁.2.2.2.1 fun x => ?_
      show h (fun k => ty₁ k (a : E) * P₁ x k) = fun k => ty₂ k (a : E) * h (P₁ x) k
      rw [← funext (hP₁.1 a x), ← hh, ← hh, map_smul]
      exact funext (hP₂.1 a _)
    exact DFunLike.congr_fun k z
  have hact : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a =>
    ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := s₁ x
      rw [← Category.assoc, ← Category.assoc, ← r₁.2.1, ← hα', ← hα', ← r₂.2.1, hcomm]
  have hlam := hD ℂ (objPol o₁ p₁) (objPol o₂ p₂) α 2 1 hα Nat.prime_two inferInstance
    fun k x y c hk _ hx hy hw => by
      obtain ⟨a, rfl⟩ := exists_div_of_pow a₁ s₁ r₁.1 hk hx
      obtain ⟨a', rfl⟩ := exists_div_of_pow a₁ s₁ r₁.1 hk hy
      have w := r₁.2.2 k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      obtain rfl := weilIs_unique_fieldPoint _ _ _ o₁.t.PP.isLB ℂ (𝟙 _) k _ _ _ _ hw w
      have w' := r₂.2.2 k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      rw [hh, hh, ← map_smul h, ← map_smul h, hα', hα', hEF] at w'
      rw [pow_one]
      exact w'
  have : IsMonHom ψ.hom := hα
  exact ⟨⟨CubeMap.ofHom α, isGrpPullback_of_iso ψ, rfl, fun a => congrArg (fun z => z.left) (hact a),
    HeckePoint.isPullCubical_of_iso hG p₁.1 α o₁.t.cub o₂.t.cub (HeckePoint.iso_of_lam o₁.t o₂.t α hact hlam)⟩,
    fun z => congrArg (fun q => q.left) (hα' z).symm⟩

theorem exists_objMap_of_coprime {D : Datum H} {l : Level H} (hA : l.A = 1) {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S)) (J : Ideal (𝓞 E))
    (hJ : l.Mb ⊔ J = ⊤)
    (h₁ : ∀ a ∈ J • (⊤ : Submodule (𝓞 E) D.La), (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : (1 : 𝟙_ (Over S) ⟶ o₁.t.G).left ≫ m.φ = (1 : 𝟙_ (Over S) ⟶ o₂.t.G).left) :
    ∃ n : ObjMap o₁ o₂ (𝟙 S), n.toSABMap.φ = m.φ := by
  refine ⟨⟨m, fun a => ?_, fun a => ?_⟩, rfl⟩
  · have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔ J • (⊤ : Submodule (𝓞 E) D.La) := by
      rw [← Submodule.sup_smul, hJ, Submodule.top_smul]
      trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
    rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
    exact (h₁ y hy).trans (Category.id_comp _).symm
  · have c₁ := o₁.etaA_ker a
    have c₂ := o₂.etaA_ker a
    rw [hA, one_smul] at c₁ c₂
    rw [c₁, c₂]
    exact h₂.trans (Category.id_comp _).symm

theorem phi_eq_of_point_eq {D : Datum H} {l : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S : Scheme.{0}} {s : S ⟶ Sp B} {s' : Sp ℂ ⟶ Sp B'}
    {o : Obj D l b s} {o₁ : Obj D l b' s'} {y y' : Sp ℂ ⟶ S} (h : y' = y) (m : ObjMap o₁ o y)
    (m' : ObjMap o₁ o y') : m'.toSABMap.φ = m.toSABMap.φ := by
  subst h
  exact objMap_unique_of_field GlobalTheory.ArcCM.known_holds.laws.serre m' m

theorem isExp_family {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ ty) (i : Fin F.n) {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) :
    GlobalTheory.UnifPoint.IsExp (F.ex i P) :=
  ⟨F.ex_add i P hP, F.ex_onto i P hP, GlobalTheory.ArcCM.isHolTo_exp_of_isPeriod F i P hP, (F.ex_diff i P hP).1,
    (F.ex_diff i P hP).2⟩

theorem pow_of_add {V Q : Type} [AddCommGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w) (n : ℕ)
    (z : V) : e (n • z) = e z ^ n := by
  induction n with
  | zero =>
    have := he 0 0
    rw [add_zero] at this
    rw [zero_smul, pow_zero]
    exact left_eq_mul.1 this
  | succ n ih => rw [succ_nsmul, he, ih, pow_succ]

theorem ex_comp_eq {D : Datum H} {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {r : Xo₂.X ⟶ Xo.X}
    (m : SABMap Xo₂.univ.t Xo.univ.t r) (pd : ℕ) (hA : l.A = 1) (hM : l₂.M = l.M * pd) (hle : l₂.Mb ≤ l.Mb)
    (heta : ∀ a, (Xo₂.univ.eta a ^ pd).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    {σ : KA l →+* ℂ} {σ₂ : KA l₂ →+* ℂ} {ty ty₂ : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (F₂ : FamilyUnif Xo₂ σ₂ ty₂) (k : Fin F.n) (k₂ : Fin F₂.n) {P : (F.Di k).La →+ (Fin g → ℂ)}
    {P₂ : (F₂.Di k₂).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di k) ty P) (hP₂ : IsPeriod (F₂.Di k₂) ty₂ P₂)
    (hy : (F₂.u k₂ P₂ ≫ r) ≫ Xo.s = spMap σ)
    (gam : (F₂.Di k₂).La ≃ₗ[𝓞 E] (F.Di k).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hEF : ∀ a b, (F.Di k).EF (gam a) (gam b) = (F₂.Di k₂).EF a b)
    (gM : ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      ∃ x, gam (F₂.t k₂ a) = F.t k a + l.M • x)
    (hh : ∀ a, P (gam a) = h (P₂ a)) :
    F₂.u k₂ P₂ ≫ r = F.u k P ∧ ∀ z, (F₂.ex k₂ P₂ z).left ≫ m.φ = (F.ex k P (h z)).left := by
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hp0 : pd ≠ 0 := fun h0 => by
    have := l₂.three_le
    rw [hM, h0] at this
    omega
  have hy' := F.over_σ k P hP
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.obj_pull E H D l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) (F₂.u k₂ P₂ ≫ r) rfl rfl
    (hy.trans (Category.id_comp _).symm) Xo.univ
  obtain ⟨o₂, ⟨m₂⟩⟩ := GlobalTheory.obj_pull E H D l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) (F.u k P) rfl rfl
    (hy'.trans (Category.id_comp _).symm) Xo.univ
  obtain ⟨n, hn⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ _ _ _ r _ (F₂.u k₂ P₂) m m₁.toSABMap rfl).1
  obtain ⟨e₁, f₁, a₁, s₁, r₁, u₁⟩ := exists_fibre_unif n hP₂ (isExp_family F₂ k₂ hP₂)
    ⟨F₂.ex_ker k₂ P₂ hP₂, F₂.ex_lin k₂ P₂ hP₂, F₂.ex_weil k₂ P₂ hP₂⟩
  obtain ⟨e₂, f₂, a₂, s₂, r₂, u₂⟩ := exists_fibre_unif m₂.toSABMap hP (isExp_family F k hP)
    ⟨F.ex_ker k P hP, F.ex_lin k P hP, F.ex_weil k P hP⟩
  obtain ⟨w, hw⟩ := exists_sabMap_types o₁ o₂ hP₂ hP a₁ s₁ s₂ r₁ r₂ u₁ u₂ gam h hEF hh
  have hmap : l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.map_mono hle
  obtain ⟨q, hq⟩ := exists_objMap_of_coprime hA o₁ o₂ w (l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
    (eq_top_iff.2 (l₂.coprime.symm.le.trans (sup_le_sup_right hle _)))
    (fun a ha => by
      have j₂ := F.ex_eta k P hP a (Submodule.smul_mono_left hmap ha)
      have j₁ : toUnit _ ≫ Xo₂.univ.eta a ^ pd = F₂.ex k₂ P₂ ((l.M : ℂ)⁻¹ • P₂ (F₂.t k₂ a)) := by
        rw [MonObj.comp_pow, F₂.ex_eta k₂ P₂ hP₂ a ha, ← pow_of_add (F₂.ex_add k₂ P₂ hP₂), hM,
          ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_mul, mul_inv, mul_left_comm,
          mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp0), _root_.mul_one]
      have c₁ : (o₁.eta a).left = (e₁ ((l.M : ℂ)⁻¹ • P₂ (F₂.t k₂ a))).left := by
        refine m₁.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
        refine (m₁.eta a).trans (Eq.trans ?_ (congrArg (_ ≫ ·) hn))
        rw [← Category.assoc (e₁ _).left, f₁, ← j₁, Category.assoc, ← heta]
        exact (Category.assoc _ _ _).symm
      have c₂ : (o₂.eta a).left = (e₂ ((l.M : ℂ)⁻¹ • P (F.t k a))).left :=
        m₂.cart.1.hom_ext ((m₂.eta a).trans ((congrArg (fun q => q.left) j₂).trans (f₂ _).symm))
          ((Over.w _).trans (Over.w _).symm)
      rw [c₁, c₂, hw, map_smul h, ← hh, (div_eq_iff hP.2.1 a₂ r₂.1 hM0 _ _).2 (gM a ha)])
    (by
      have := hw 0
      rwa [map_zero, (r₁.1 0).2 (zero_mem _), (r₂.1 0).2 (zero_mem _)] at this)
  obtain ⟨q', hq'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 (F.u k P)
    (𝟙 _) m₂).1 q
  have hyy : F₂.u k₂ P₂ ≫ r = 𝟙 _ ≫ F.u k P :=
    (GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel E H D l Xo ℂ (baseOfEmb σ) σ _ (𝟙 _) o₁ inferInstance rfl
      rfl).unique ⟨hy.trans (Category.id_comp _).symm, ⟨m₁⟩⟩
      ⟨by rw [Category.id_comp, hy', Category.id_comp], ⟨q'⟩⟩
  have hφ := phi_eq_of_point_eq hyy.symm m₁ q'
  refine ⟨hyy.trans (Category.id_comp _), fun z => ?_⟩
  rw [← f₁, ← f₂, ← hw, Category.assoc, Category.assoc, hn, ← hq, ← hq', hφ]

end GlobalTheory.CoverExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarMemCoefficientRingAuxiliaryLevel
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.FlipScalUnit

open Formalism.L2.Host

theorem locK_eq_val_zpow {L : Type} [Field L] [NumberField L] (χ : HChar L) (R : HeightOneSpectrum (𝓞 L))
    (hR : χ.UnrAt R) (m : Lˣ) : χ.locK R m = χ.val R ^ ordF R m := by
  set N := ordF R m with hN
  set u : Lˣ := m * (unif R ^ N)⁻¹ with hu
  have hmu : m = u * unif R ^ N := by rw [hu, inv_mul_cancel_right]
  have hPv : R.valuation L (m : L) = WithZero.exp (-N) := by
    have h0 : R.valuation L (m : L) ≠ 0 := by simp
    rw [hN, ordF, neg_neg]
    exact (WithZero.exp_log h0).symm
  have hatFin : ∀ (x : Lˣ), Valued.v ((atFin R x : (R.adicCompletion L)ˣ) : R.adicCompletion L) = R.valuation L (x : L) :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' R (x : L)
  have hunit : IsUnitAt R (atFin R u) := by
    have h1 := unif_spec R
    unfold IsUnifAt at h1
    unfold IsUnitAt
    rw [hu, map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h1, hatFin, hPv, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have h1 : χ.locK R u = 1 := hR _ hunit
  calc χ.locK R m = χ.locK R (u * unif R ^ N) := by rw [← hmu]
    _ = χ.val R ^ N := by rw [map_mul, map_zpow, h1, one_mul]; rfl


open Formalism.L2.JoinChr in
set_option maxHeartbeats 800000 in
theorem char_flipDet {D : D7} (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (he : IsIdemSum e T) (m : D.host.Eˣ) (x : (AE D)ˣ)
    (hx : (x : AE D) * (e * incA D (m : D.host.E) + (1 - e)) = 1) :
    ((c x : Circle) : ℂ) = ∏ R ∈ T, ((χ.locK R m⁻¹ : ℂˣ) : ℂ) := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  have hinf : infPart D (x : AE D) = 1 := by
    have h0 := congrArg (infPart D) hx
    simp only [map_mul, map_add (f := _), map_sub, map_one, GlobalTheory.PlaceVec.idemSum_infPart he, zero_mul, zero_add, sub_zero,
      mul_one] at h0
    exact h0
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ R : HeightOneSpectrum (𝓞 D.host.E), AE D →+* R.adicCompletion D.host.E,
      ∀ R z, ev R z = GlobalTheory.CharLocProd.evalAt R (ι (finPart D z)) :=
    ⟨fun R => (GlobalTheory.CharLocProd.evalAt R).comp ((ι : _ →+* _).comp (finPart D)), fun _ _ => rfl⟩
  have hidem : ∀ Q ∈ T, ev Q (es Q) = 1 ∧ ∀ R, R ≠ Q → ev R (es Q) = 0 := by
    intro Q hQ
    simp only [hev]
    refine GlobalTheory.TameSplitChar.idem_apply _ (by rw [← RingEquiv.map_mul, ← RingHom.map_mul, (hes Q hQ).1.1]) Q fun y hy => ?_
    refine ((hes Q hQ).2 y hy).trans (not_congr ((h2 _).trans ?_))
    rw [RingHom.map_mul, RingEquiv.map_mul, show finPart D (incA D ((y : D.host.E)⁻¹)) =
      (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((y : D.host.E)⁻¹) from rfl, h1]
    rfl
  have heT : ∀ R ∈ T, ev R e = 1 := by
    intro R hR
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum, Finset.sum_eq_single R, (hidem R hR).1]
    · intro Q hQ hne; exact (hidem Q hQ).2 R hne.symm
    · intro h; exact absurd hR h
  have heT' : ∀ R, R ∉ T → ev R e = 0 := by
    intro R hR
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q hQ => (hidem Q hQ).2 R fun h => hR (h ▸ hQ)
  have hinc : ∀ R (k : D.host.E), ev R (incA D k) = algebraMap D.host.E (R.adicCompletion D.host.E) k := by
    intro R k
    rw [hev, show finPart D (incA D k) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] k from rfl, h1,
      GlobalTheory.CharLocProd.evalAt_algebraMap]
  have hxT : ∀ R ∈ T, ev R x = algebraMap D.host.E (R.adicCompletion D.host.E) ((m⁻¹ : D.host.Eˣ) : D.host.E) := by
    intro R hR
    have h0 := congrArg (ev R) hx
    simp only [map_mul, map_add (f := _), map_sub, map_one, heT R hR, one_mul, sub_self, add_zero, hinc] at h0
    rw [eq_inv_of_mul_eq_one_left h0, Units.val_inv_eq_inv_val, map_inv₀]
  have hxT' : ∀ R, R ∉ T → ev R x = 1 := by
    intro R hR
    have h0 := congrArg (ev R) hx
    simp only [map_mul, map_add (f := _), map_sub, map_one, heT' R hR, zero_mul, zero_add, sub_zero, mul_one] at h0
    exact h0
  have hfin : {R : HeightOneSpectrum (𝓞 D.host.E) | R.asIdeal ∣ Ideal.span {(N : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hN.ne')
  have key := hprod x hinf (T ∪ hfin.toFinset) (fun R => if R ∈ T then m⁻¹ else 1) ?_ ?_
  rotate_left
  · intro R _
    change Valued.v (GlobalTheory.CharLocProd.evalAt R (ι (finPart D x))) = _ ∧
      Valued.v (GlobalTheory.CharLocProd.evalAt R (ι (finPart D x)) - _) ≤ _
    rw [← hev]
    by_cases hR : R ∈ T
    · simp only [if_pos hR]
      rw [hxT R hR, sub_self, map_zero, GlobalTheory.CharLocProd.val_algebraMap]
      exact ⟨rfl, zero_le'⟩
    · simp only [if_neg hR]
      rw [hxT' R hR, Units.val_one, map_one, map_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le'⟩
  · intro R hR
    rw [Finset.mem_union, not_or] at hR
    change Valued.v (GlobalTheory.CharLocProd.evalAt R (ι (finPart D x))) = _ ∧ _
    rw [← hev, hxT' R hR.1, map_one]
    exact ⟨rfl, fun h => hR.2 (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 h))⟩
  rw [key, ← Finset.prod_subset Finset.subset_union_left
    (fun R _ hR => by rw [if_neg hR, map_one, Units.val_one])]
  exact Finset.prod_congr rfl fun R hR => by rw [if_pos hR]

end GlobalTheory.FlipScalUnit


open GlobalTheory.FlipScalUnit in
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l pd : ℕ), ChiData χW χ M₀ → l.Prime → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime pd (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT pd x → flipScal χW V W T pd x ∈ O := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hv hodd χ M₀ l pd hχ hl hpM hpl hpbad k _ _ σ la O hla hVR hConj hVI T eT x hT
    hpT hx
  classical
  have hpair := hv.1
  have hpd0 : pd ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' ((Nat.coprime_zero_left l).1 hpl)
  have hnot : ∀ (a b : ℕ), Nat.Coprime a b → ∀ R : HeightOneSpectrum (𝓞 D.host.E),
      ((a : ℕ) : 𝓞 D.host.E) ∈ R.asIdeal → ((b : ℕ) : 𝓞 D.host.E) ∉ R.asIdeal := by
    intro a b hab R ha hb
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
    have h1 : (((u * a + v * b : ℤ)) : 𝓞 D.host.E) = 1 := by rw [huv]; simp
    apply R.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← h1]
    push_cast
    exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
  have hu : ∀ R ∈ T, χ.UnrAt R := fun R hR => hχ.2.1 R (hnot pd M₀ hpM R (hpT R hR))
  have hlR : ∀ R ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ R.asIdeal := fun R hR => hnot pd l hpl R (hpT R hR)
  have hO : ∀ m : ℕ, Nat.Coprime m l → ((m : ℂ))⁻¹ ∈ O := fun m hm => by
    have h1 := hVR ((m : k)⁻¹) (by rw [map_inv₀, GlobalTheory.ScalarUnit.val_natCast la hla hm, inv_one])
    simpa using h1
  letI : Algebra k ℂ := σ.toAlgebra
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_valuationSubring_over (Ω := ℂ) la
  have hA' : ∀ x : 𝓞 k, A.valuation (σ (x : k)) < 1 ↔ x ∈ la.asIdeal := hA
  have hpA : (l : ℂ) ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    have h1 := (hA' (l : 𝓞 k)).2 hla
    simpa using h1
  choose bW hbW using hpair.expW
  have hval : ∀ R ∈ T, ((χ.val R : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) ∈ O := by
    intro R hR
    obtain ⟨y, hy⟩ := hVI R (hu R hR)
    have hy' : σ y = ((χ.val R : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) := by
      rw [hy, Formalism.L2.Host.HChar.valTw, GlobalTheory.LevelSeriesScal.natCast_cpow_half]
    obtain ⟨h1, -⟩ := GlobalTheory.LevelSeriesScal.val_mul_sqrt_unit D χW χ hχ.1 _ hbW l A hl hpA R (hlR R hR)
    rw [← hy'] at h1
    have hy0 : la.valuation k y ≤ 1 :=
      GlobalTheory.LevelSeriesScal.val_le_one_of_mem σ la A hA' y ((A.valuation_le_one_iff _).2 h1)
    exact hy' ▸ hVR y hy0
  have hNl : ∀ R ∈ T, Nat.Coprime (Ideal.absNorm R.asIdeal) l := by
    intro R hR
    have hle : Ideal.span {((pd : ℕ) : 𝓞 D.host.E)} ≤ R.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 (hpT R hR)
    have hd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 D.host.E)) pd, Algebra.norm_algebraMap,
      Int.natAbs_pow, Int.natAbs_natCast] at hd
    exact Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.pow_left _ hpl)
  have hN0 : ∀ R : HeightOneSpectrum (𝓞 D.host.E), Ideal.absNorm R.asIdeal ≠ 0 := fun R h =>
    R.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  set mU : D.host.Eˣ := Units.mk0 ((pd : ℕ) : D.host.E) (by exact_mod_cast hpd0) with hmU
  set nR : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun R =>
    (Associates.mk R.asIdeal).count (Associates.mk (Ideal.span {((pd : ℕ) : 𝓞 D.host.E)})).factors with hnR
  have hord : ∀ R : HeightOneSpectrum (𝓞 D.host.E), Formalism.L2.Host.ordF R mU = (nR R : ℤ) := by
    intro R
    have h0 : ((pd : ℕ) : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hpd0
    have e1 : ((mU : D.host.Eˣ) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E ((pd : ℕ) : 𝓞 D.host.E) := by
      rw [hmU, Units.val_mk0, map_natCast]
    unfold Formalism.L2.Host.ordF
    rw [e1, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def, if_neg h0, WithZero.log_exp,
      neg_neg]
  have hx' : (x : AE D) * (eT * incA D ((mU ^ V.rank : D.host.Eˣ) : D.host.E) + (1 - eT)) = 1 := by
    have h := hx
    unfold IsFlipDet at h
    rwa [Units.val_pow_eq_pow_val, map_pow, hmU, Units.val_mk0, map_natCast]
  have hcx := char_flipDet χW χ hχ.1 T eT hT (mU ^ V.rank) x hx'
  have hcx' : ((χW x : Circle) : ℂ) = ∏ R ∈ T, (((χ.val R : ℂˣ) : ℂ) ^ (nR R * V.rank))⁻¹ := by
    rw [hcx]
    refine Finset.prod_congr rfl fun R hR => ?_
    rw [map_inv, map_pow, locK_eq_val_zpow χ R (hu R hR), hord R, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      zpow_natCast, Units.val_pow_eq_pow_val, ← pow_mul]
  have hsq : Real.sqrt ((flipIdx V W T pd : ℕ) : ℝ) =
      ∏ R ∈ T, Real.sqrt (Ideal.absNorm R.asIdeal) ^ (nR R * V.rank * W.rank) := by
    have hnn : 0 ≤ ∏ R ∈ T, Real.sqrt (Ideal.absNorm R.asIdeal) ^ (nR R * V.rank * W.rank) :=
      Finset.prod_nonneg fun _ _ => pow_nonneg (Real.sqrt_nonneg _) _
    rw [← Real.sqrt_sq hnn]
    congr 1
    unfold flipIdx
    rw [← Finset.prod_pow]
    push_cast
    refine Finset.prod_congr rfl fun R _ => ?_
    unfold HeightOneSpectrum.maxPowDividing
    have hsN : Real.sqrt (Ideal.absNorm R.asIdeal : ℝ) ^ 2 = (Ideal.absNorm R.asIdeal : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg _)
    rw [map_pow, Nat.cast_pow]
    conv_lhs => rw [← hsN]
    simp only [hnR, ← pow_mul]
    ring_nf
  obtain ⟨s, hs⟩ := hodd
  have hfac : flipScal χW V W T pd x = ∏ R ∈ T, ((((χ.val R : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ)) ^
      (nR R * V.rank) * (((Ideal.absNorm R.asIdeal ^ (nR R * V.rank * (s + 1)) : ℕ) : ℂ))⁻¹) := by
    unfold flipScal
    rw [hcx', hsq, ← Finset.prod_inv_distrib, Complex.ofReal_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun R _ => ?_
    have hs0 : ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
      exact_mod_cast Nat.pos_of_ne_zero (hN0 R)
    have h2 : ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) ^ 2 = ((Ideal.absNorm R.asIdeal : ℕ) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast
      rfl
    rw [inv_inv, Complex.ofReal_pow, Nat.cast_pow, ← h2, hs, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [hfac]
  exact prod_mem fun R hR => O.mul_mem (O.pow_mem (hval R hR) _) (hO _ (Nat.Coprime.pow_left _ (hNl R hR)))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralRankinSelbergThetaEqWhittakerUnfoldingStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_rankinSelbergTheta_eq_whittakerUnfolding : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a), (ℓ : ℕ) + 1 = a →
    ∀ (π : CuspSub E a), π.IsUnitary → ∀ (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕₀ : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ → ∀ x : ℝ,
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ =
    ∫⁻ g in 𝓕₀, ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit F) (GlobalTheory.JSW.whit F) Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ := by
  first | (exact @GlobalTheory.RSUnfold.lintegral_theta_eq_whit) | (exact GlobalTheory.RSUnfold.lintegral_theta_eq_whit) | (intros; apply GlobalTheory.RSUnfold.lintegral_theta_eq_whit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLatticeIndex_cartanDecomposition_eq_normPow : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.LFun.IsFrameAt w (frameLat T) a → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), ∀ g : GlobalTheory.FinZeta.Gv T v, GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g = a * (k₁ * t * k₂) * a⁻¹ → GlobalTheory.LocKerMod.idxAt T w h g = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := by
  first | exact @GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow | exact GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow | (intros; apply GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardCosocleGLHolds
section
namespace GlobalTheory

theorem standardCosocleGL_holds : GlobalTheory.Published.StandardCosocleGL :=
  CompanionTheory.Exh.standardCosocleGL_of_seg CompanionTheory.RgGu.segmentRepresentation

end GlobalTheory
end

