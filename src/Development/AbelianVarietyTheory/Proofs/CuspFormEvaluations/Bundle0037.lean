module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InvariantOperatorValueTriangularChange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointGeneratorRingBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace GenBaseChange

open VVRank EmbPull TopologicalSpace

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

theorem isGenSec_pullS (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [IsAffine T.left] [IsAffine T'.left] (h : T' ⟶ T)
    {th : LB.Sec (LPow P.A P.L 1 T)} (H : IsGenSec P.A P.L 1 th) : IsGenSec P.A P.L 1 (pullS P.A 1 h th) := by
  intro s
  let I : Ideal Γ(T'.left, ⊤) := (Submodule.span Γ(T'.left, ⊤)
    {pullM P.A P.L 1 h (SecM.ofSec P.A th)}).comap (LinearMap.toSpanSingleton _ _ (SecM.ofSec P.A s))
  have key : ∀ p : T'.left, ∃ f ∈ I, p ∈ T'.left.basicOpen f := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom (h.left p))
    have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    obtain ⟨f, hf, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨h.left p, hV⟩ trivial
    let f' := h.left.appTop.hom f
    have hf' : h.left ⁻¹ᵁ T.left.basicOpen f = T'.left.basicOpen f' := Scheme.preimage_basicOpen_top _ _
    let W := T.left.basicOpen f
    let W' := T'.left.basicOpen f'
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
      (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
    let k₀ : W'.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (W'.ι ≫ h.left) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hf'.ge y.2)
    have hk₀ : k₀ ≫ W.ι = W'.ι ≫ h.left := IsOpenImmersion.lift_fac _ _ _
    let k : overRes W' ⟶ overRes W := Over.homMk k₀ (by
      change k₀ ≫ W.ι ≫ T.hom = W'.ι ≫ T'.hom
      rw [← Category.assoc, hk₀, Category.assoc, Over.w])
    have hk : k ≫ overResι W = overResι W' ≫ h := Over.OverMorphism.ext hk₀
    have hW' : IsAffineOpen W' := (isAffineOpen_top _).basicOpen f'
    have : IsAffine (overRes W').left := hW'
    obtain ⟨c, hc⟩ := exists_basis P 1 b hb (overRes W') (k ≫ l)
    obtain ⟨n, u, hu⟩ := exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))
    obtain ⟨r, hr⟩ := H (SecM.toSec P.A u)
    have hr' : u = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
    have e₁ := congrArg (pullM P.A P.L 1 k) hu
    rw [LinearMap.map_smulₛₗ, pullM_comp _ P.isLB, pullM_comp _ P.isLB, hk, ← pullM_comp _ P.isLB, hr',
      LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ] at e₁
    have e₂ : k.left.appTop.hom ((overResι W).left.appTop.hom (f ^ n)) = (overResι W').left.appTop.hom (f' ^ n) :=
      (congrArg (fun q => q.left.appTop.hom (f ^ n)) hk).trans
        (congrArg (overResι W').left.appTop.hom (map_pow h.left.appTop.hom f n))
    rw [e₂] at e₁
    obtain ⟨d, hd⟩ : ∃ d : Γ((overRes W').left, ⊤), pullM P.A P.L 1 (overResι W') (SecM.ofSec P.A s) =
        d • pullM P.A P.L 1 (k ≫ l) (SecM.ofSec P.A (b hq.default)) := by
      have := c.sum_repr (pullM P.A P.L 1 (overResι W') (SecM.ofSec P.A s))
      rw [Fintype.sum_unique, hc] at this
      exact ⟨_, this.symm⟩
    obtain ⟨m, d₀, hd₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T'.left, ⊤)), (overResι W').left.appTop.hom d₀ =
        (overResι W').left.appTop.hom (f' ^ m) * d := exists_pow_mul_extend f' d
    obtain ⟨N, hN⟩ := exists_pow_kill_secM P 1 f' ((f' ^ m * f' ^ n) • SecM.ofSec P.A s -
      (d₀ * h.left.appTop.hom r) • pullM P.A P.L 1 h (SecM.ofSec P.A th))
        (map_sub_eq_zero _ _ _ _ _ _ _ _ _ d e₁ hd hd₀)
    refine ⟨f' ^ N * (f' ^ m * f' ^ n), Submodule.mem_span_singleton.2 ⟨f' ^ N * (d₀ * h.left.appTop.hom r), ?_⟩, ?_⟩
    · rw [smul_sub, sub_eq_zero, ← mul_smul, ← mul_smul] at hN
      exact hN.symm
    · have hp' : p ∈ T'.left.basicOpen f' := hf'.le hp
      rw [Scheme.mem_basicOpen_top] at hp' ⊢
      simp only [map_mul, map_pow]
      exact (hp'.pow _).mul ((hp'.pow _).mul (hp'.pow _))
  have hI : Ideal.span (I : Set Γ(T'.left, ⊤)) = ⊤ :=
    (isAffineOpen_top T'.left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨f, hf, hp⟩ := key p
      exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hI
  rw [LinearMap.toSpanSingleton_apply, one_smul] at hr
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

theorem gs_eq_zero {Y : Scheme.{0}} (f a : Γ(Y, ⊤)) (n : ℕ) (h : (Y.basicOpen f).ι.appTop.hom (a * f ^ n) = 0)
    (p : Y) (hp : p ∈ Y.basicOpen f) : gs (𝟙 Y) p ⊤ a = 0 := by
  let z : (Y.basicOpen f).toScheme := ⟨p, hp⟩
  have q := (gs_pull (𝟙 _) (Y.basicOpen f).ι z ⊤ trivial (a * f ^ n)).symm.trans
    ((congrArg (gs (𝟙 _) z _) h).trans (LBGerm.gs_zero _ z _ trivial))
  rw [Category.id_comp] at q
  replace q := (gs_stalkMap (Y.basicOpen f).ι z ⊤ trivial _).symm.trans q
  have q' : gs (𝟙 Y) p ⊤ (a * f ^ n) = 0 := PushInv.stalk_inj (Y.basicOpen f).ι z (q.trans (map_zero _).symm)
  rw [gs_mul _ p ⊤ trivial, LBGerm.gs_pow _ p ⊤ trivial] at q'
  have hu : IsUnit (gs (𝟙 Y) p ⊤ f) := by
    rw [gs_eq _ p ⊤ trivial]
    exact (Scheme.mem_basicOpen_top _ _ _).1 hp
  exact (hu.pow n).mul_left_eq_zero.1 q'

theorem basis_smul_eq_zero {R M κ : Type} [CommRing R] [AddCommGroup M] [Module R M] (c : Module.Basis κ R M) (i : κ)
    (x : R) (h : x • c i = 0) : x = 0 := by
  simpa using congrArg (fun q => c.repr q i) h

theorem eq_zero_of_smul (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [IsAffine T.left]
    {th : LB.Sec (LPow P.A P.L 1 T)} (H : IsGenSec P.A P.L 1 th) (a : Γ(T.left, ⊤))
    (ha : a • (SecM.ofSec P.A th : SecM P.A P.L 1 T) = 0) : a = 0 := by
  refine fn_ext fun p _ => Eq.trans ?_ (LBGerm.gs_zero _ p ⊤ trivial).symm
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨f, hf, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial
  let W := T.left.basicOpen f
  let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
    (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have : IsAffine (overRes W).left := hW
  obtain ⟨c, hc⟩ := exists_basis P 1 b hb (overRes W) l
  obtain ⟨n, u, hu⟩ := exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))
  obtain ⟨r, hr⟩ := H (SecM.toSec P.A u)
  have hr' : u = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
  have h0 : a • u = 0 := by rw [hr', smul_comm, ha, smul_zero]
  have e := congrArg (pullM P.A P.L 1 (overResι W)) h0
  rw [LinearMap.map_smulₛₗ, map_zero, hu, ← mul_smul, ← map_mul] at e
  have e' : (overResι W).left.appTop.hom (a * f ^ n) • c hq.default = 0 := by
    rw [hc]; exact e
  have e₂ := basis_smul_eq_zero c _ _ e'
  exact gs_eq_zero f a n e₂ p hp

theorem existsUnique_of_isPullSec (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [IsAffine T.left] [IsAffine T'.left]
    (h : T' ⟶ T) {th : LB.Sec (LPow P.A P.L 1 T)} (H : IsGenSec P.A P.L 1 th) {th' : LB.Sec (LPow P.A P.L 1 T')}
    (hp : IsPullSec P.A P.L 1 (h ▷ P.A) (whiskerRight_snd _ _) th th') (s : LB.Sec (LPow P.A P.L 1 T')) :
    ∃! r : Γ(T'.left, ⊤), ∀ j, s.f j = liftFun P.A _ r * th'.f j := by
  have H' : IsGenSec P.A P.L 1 th' := fun s => by
    obtain ⟨r, hr⟩ := isGenSec_pullS P hS h H s
    exact ⟨r, fun j => (hr j).trans (congrArg (_ * ·) (hp j).symm)⟩
  obtain ⟨r, hr⟩ := H' s
  refine ⟨r, hr, fun r' hr' => sub_eq_zero.1 (eq_zero_of_smul P hS H' _ ?_)⟩
  rw [sub_smul, sub_eq_zero]
  exact Subtype.ext (funext fun j => (hr' j).symm.trans (hr j))

theorem toΓ_bijective (R : Type) [CommRing R] : Function.Bijective (toΓ R) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv

end GenBaseChange

theorem framedPoint_generator_baseChange :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] (ψ : S →+* T) (y : FrPt Xo c S) (h : ptO Xo (spMap ψ ≫ y.x) ⟶ ptO Xo y.x), h.left = spMap ψ → ∀ s' : LB.Sec (PPx (spMap ψ ≫ y.x)), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s s' → ∀ s'' : LB.Sec (PPx (spMap ψ ≫ y.x)), ∃! a : T, ∀ i, s''.f i = scal (spMap ψ ≫ y.x) a i * s'.f i := by
  intro hL E _ _ _ H Dw l Xo c S T _ _ _ ψ y h _ s' hs' s''
  have := UnivPol.isLocallyNoetherian Xo
  have : IsAffine (ptO Xo y.x).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (ptO Xo (spMap ψ ≫ y.x)).left := inferInstanceAs (IsAffine (Spec _))
  obtain ⟨r, hr, hu⟩ := GenBaseChange.existsUnique_of_isPullSec (UnivPol.pol Xo) hL.secBaseChange h
    (th := y.s) (fun s => by
      obtain ⟨a, ha, -⟩ := y.gen s
      exact ⟨toΓ S a, ha⟩) (th' := s') hs' s''
  obtain ⟨a, rfl⟩ := (GenBaseChange.toΓ_bijective T).2 r
  exact ⟨a, hr, fun a' ha' => (GenBaseChange.toΓ_bijective T).1 (hu _ ha')⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicSumTriangularFrameChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TriangularFrame

theorem basis_of_triangular {T : Type} [Fintype T] {r : T → ℕ} {S : Type} [CommRing S] {d : ℕ}
    (u : (Σ τ : T, Fin (r τ)) → Fin d → S) (cf : ∀ τ : T, Fin (r τ) → Fin (r τ) → S)
    (h0 : ∀ τ i j, i < j → cf τ i j = 0) (h1 : ∀ τ i, IsUnit (cf τ i i))
    (hb : ∀ v : Fin d → S, ∃! a : (Σ τ : T, Fin (r τ)) → S, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) (v : Fin d → S) :
    ∃! a : (Σ τ : T, Fin (r τ)) → S, ∀ e, ∑ ℓ, a ℓ * (∑ j, cf ℓ.1 ℓ.2 j * u ⟨ℓ.1, j⟩ e) = v e := by
  classical
  have hdet : ∀ τ, IsUnit (Matrix.of (cf τ)).det := fun τ => by
    rw [Matrix.det_of_lowerTriangular (Matrix.of (cf τ)) (fun i j hij => h0 τ i j (by simpa using hij))]
    exact IsUnit.prod_iff.2 fun i _ => h1 τ i
  have key : ∀ (a : (Σ τ : T, Fin (r τ)) → S) e, ∑ ℓ, a ℓ * (∑ j, cf ℓ.1 ℓ.2 j * u ⟨ℓ.1, j⟩ e) =
      ∑ ℓ : (Σ τ : T, Fin (r τ)), Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1)) ℓ.2 * u ℓ e := by
    intro a e
    rw [Fintype.sum_sigma, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    simp only [_root_.mul_assoc]
    exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (i j : Fin (r τ)) => a ⟨τ, i⟩ * (cf τ i j * u ⟨τ, j⟩ e))
  simp only [key]
  obtain ⟨b, hb1, hb2⟩ := hb v
  have back : ∀ a : (Σ τ : T, Fin (r τ)) → S,
      (∀ e, ∑ ℓ : (Σ τ : T, Fin (r τ)), Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1)) ℓ.2 * u ℓ e = v e) →
      a = fun ℓ => Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))⁻¹ ℓ.2 := by
    intro a ha
    have := hb2 _ ha
    subst this
    funext ℓ
    show _ = Matrix.vecMul (Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))) _ _
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (hdet _), Matrix.vecMul_one]
  refine ⟨fun ℓ => Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))⁻¹ ℓ.2, fun e => ?_, back⟩
  rw [← hb1 e]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  congr 1
  show Matrix.vecMul (Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))⁻¹) _ _ = _
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hdet _), Matrix.vecMul_one]

theorem fst_comp_jetTan {S : Type} [CommRing S] {κ : Type} [DecidableEq κ] (ℓ : κ) :
    (TrivSqZeroExt.fstHom S S S).comp (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S) = jetAug := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show TrivSqZeroExt.fst (MvPolynomial.aeval
    (fun i => if i = ℓ then (DualNumber.eps : DualNumber S) else 0) (MvPolynomial.X i : MvPolynomial κ S)) =
    MvPolynomial.aeval (fun _ => (0 : S)) (MvPolynomial.X i : MvPolynomial κ S)
  by_cases h : i = ℓ <;> simp [h]

theorem left_one {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  show (toUnit X ≫ η[M]).left = _
  rw [Over.comp_left]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem isTanAt_jetTan {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {κ : Type} [DecidableEq κ]
    (x : overAt x0 (Jet S κ (0 + 1)) ⟶ Xo.univ.t.G)
    (hx : homAt x0 (jetAug : Jet S κ (0 + 1) →ₐ[S] S) ≫ x = 1) (ℓ : κ) :
    IsTanAt x0 (homAt x0 (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S) ≫ x).left := by
  refine ⟨Over.w _, ?_⟩
  have h1 := congrArg (fun f => f.left) hx
  simp only [Over.comp_left, left_one] at h1 ⊢
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫
      (homAt x0 (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S)).left =
      (homAt x0 (jetAug : Jet S κ (0 + 1) →ₐ[S] S)).left := by
    rw [← fst_comp_jetTan ℓ]
    exact (Spec.map_comp _ _).symm
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ x.left) e)).trans (h1.trans ?_)
  have e' : spMap (algebraMap S S) = 𝟙 _ := Spec.map_id _
  show (spMap (algebraMap S S) ≫ x0) ≫ _ = x0 ≫ _
  rw [e', Category.id_comp]

theorem eq_of_isPullSec_id {X : Scheme.{0}} (A : Over X) [GrpObj A] (L : LB A.left) (k : ℤ) (T : Over X)
    (F F' : LB.Sec (LPow A L k T)) (h : IsPullSec A L k (𝟙 T ▷ A) (whiskerRight_snd _ _) F F') : F' = F := by
  have key : ∀ (g : T ⊗ A ⟶ T ⊗ A) (hg : g ≫ snd T A = snd T A), g = 𝟙 _ → IsPullSec A L k g hg F F' → F' = F := by
    intro g hg e h
    subst e
    obtain ⟨f, hf⟩ := F
    obtain ⟨f', hf'⟩ := F'
    congr
    funext j
    refine (h j).trans ?_
    show ((T ⊗ A).left.presheaf.map (𝟙 _)).hom (f j) = f j
    rw [CategoryTheory.Functor.map_id]
    rfl
  exact key _ _ (MonoidalCategory.id_whiskerRight _ _) h

theorem sum_eq (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (ho u' h1 h2 h3 s' h4)
    (cf : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → S)
    (h0 : ∀ τ i j, i < j → cf τ i j = 0) (hu : ∀ τ i, IsUnit (cf τ i i))
    (hcomb : ∀ τ i, IsCombAt y.x (y.u τ) (cf τ i) (u' τ i)) (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (k : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
        ∏ b, nab (⟨y.x, ho, u', h1, h2, h3, s', h4⟩ : FrPt Xo c S) k (F b) (colOf m b) =
      (∏ ℓ : Lt1 Dw, cf ℓ.1 ℓ.2 ℓ.2 ^ a (ℓ.1, ℓ.2)) *
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y k (F b) (colOf m b) := by
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  set y' : FrPt Xo c S := ⟨y.x, ho, u', h1, h2, h3, s', h4⟩ with hy'
  obtain ⟨C, hex, hpin⟩ := hnab.2 S y
  obtain ⟨C', hex', hpin'⟩ := hnab.2 S y'
  choose f hf using fun b => hex k (F b)
  choose f' hf' using fun b => hex' k (F b)
  let uv : Lt1 Dw → Fin C.d → S := fun ℓ e => ∑ j, cf ℓ.1 ℓ.2 j * C.uvec ⟨ℓ.1, j⟩ e
  let D : ChartAt Xo c y' :=
    ⟨C.d, C.B, uv, C.x, C.e, C.wP, C.h,
      ⟨C.chart.zero, C.chart.trunc, C.chart.law, C.chart.act, fun ℓ => by
        have := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x _
          (fun j => isTanAt_jetTan y.x (C.x 1) (C.chart.zero 1) ((0 : Fin 1), j)) (y.u ℓ.1)
          (Matrix.of fun e j => C.uvec ⟨ℓ.1, j⟩ e) (cf ℓ.1 ℓ.2) (u' ℓ.1 ℓ.2)
          (fun i => C.chart.tan ⟨ℓ.1, i⟩) (hcomb ℓ.1 ℓ.2)
        have e : (Matrix.of fun e j => C.uvec ⟨ℓ.1, j⟩ e).mulVec (cf ℓ.1 ℓ.2) = uv ℓ := by
          funext e
          simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, uv]
          exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
        rw [e] at this
        exact this,
        basis_of_triangular C.uvec cf h0 hu C.chart.basis⟩,
      ⟨C.frame.gen, C.frame.ph1, C.frame.ph2, C.frame.sy, C.frame.ad⟩, C.prim, C.gauge, C.rig0⟩
  obtain ⟨N, hN, hNP, hsupp⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  have hI := hC E H Dw l Xo c hnab.1 S y' C' D k n F f' f hf' hf a _ hNP
  have hNu : IsUnit (algebraMap c.F S (N : c.F)) :=
    (IsUnit.mk0 (N : c.F) (Nat.cast_ne_zero.2 hN.ne')).map _
  have hsc : ∀ (C₀ : ChartAt Xo c y') (g : Fin n → MvPowerSeries (Fin 1 × Fin C₀.d) S),
      chartVal C₀ k g ((N : c.F) • P) = algebraMap c.F S (N : c.F) * chartVal C₀ k g P := by
    intro C₀ g
    simp only [chartVal, hsupp, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, Finset.mul_sum, _root_.mul_assoc]
  rw [hsc, hsc] at hI
  have hI' := hNu.mul_left_cancel hI
  have e₁ : ∀ m, ∏ b, nab y k (F b) (colOf m b) =
      ∏ b, C.B.nabVal S C.h H.w0 k (f b) C.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin k (F b) (f b) (hf b) (colOf m b)
  have e₂ : ∀ m, ∏ b, nab y' k (F b) (colOf m b) =
      ∏ b, C'.B.nabVal S C'.h H.w0 k (f' b) C'.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin' k (F b) (f' b) (hf' b) (colOf m b)
  simp only [e₁]
  exact (Finset.sum_congr rfl fun m _ => congrArg _ (e₂ m)).trans <| hI'.trans (_root_.GlobalTheory.nabVal_triangular E H Dw l c S C.d C.B C.h C.gauge k n f C.uvec uv cf h0 (fun _ _ _ => rfl) hu a P hP)

theorem harmonic_sum_frBor : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = 𝟙 _ → ∀ (n : ℕ), ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) → ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) = (∏ ℓ : Lt1 Dw, ((t (some ℓ) : Sˣ) : S) ^ a (ℓ.1, ℓ.2)) * ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab S _ _ y y' t hb h hh n a P hP N
  obtain ⟨x', ho, u', h1, h2, h3, s', h4⟩ := y'
  obtain ⟨hx, hcf, -⟩ := hb
  dsimp only at hx
  subst hx
  choose cf hd h0 hcomb using hcf
  have e : h = 𝟙 _ := Over.OverMorphism.ext hh
  subst e
  have hk : ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) := (Nat.cast_pow N 2).symm
  generalize ((N : ℤ) ^ 2) = K at hk
  subst hk
  intro F F' hF
  have hFF : F' = F := funext fun b => eq_of_isPullSec_id _ _ _ _ _ _ (hF b)
  subst hFF
  have := sum_eq hC nab hnab y ho u' h1 h2 h3 s' h4 cf h0 (fun τ i => by rw [hd]; exact Units.isUnit _) hcomb
    n a P hP (N ^ 2) F'
  simp only [hd] at this
  exact this

end GlobalTheory.TriangularFrame
end
end

