module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocDerRegularCoeff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaBaseChange

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

theorem isThetaPtOver_pull_of_gen {n : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)}
    (H : IsThetaPtOver P n x v) (h : T' ⟶ T)
    (hg : ∀ th, IsGenSec P.A P.L 1 th → IsGenSec P.A P.L 1 (pullS P.A 1 h th)) :
    IsThetaPtOver P n (fun a => h ≫ x a) (fun a => h.left.appTop.hom (v a)) := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨α', hα', k₁⟩ := exists_twist_pull P.A (ψ := mulT P.A T n) (hm := lift_snd _ _) (b := 1)
    hL hα h (ψ' := mulT P.A T' n) (lift_snd _ _) (mulT_comm P.A h n)
  obtain ⟨τ', hτ', k₂⟩ := exists_gen_pullTo (φ' := fun _ : Fin 1 => (1 : T' ⟶ P.A).left) τ hτ h.left
    (fun _ => by rw [← Over.comp_left, MonObj.comp_one])
  choose U' hU' k₃ using fun a => exists_symLift_act_pull hL h (hU a)
  refine ⟨_, _, α', τ', U', fun a => pullS P.A _ h (s₂ a), fun a => h.left.appTop.hom (w a),
    Units.map h.left.appTop.hom.toMonoidHom u, hg _ hth, hα', hτ', k₁ _ _ hs₁, hU',
    fun a => k₃ a _ _ (hs₂ a), fun a => isValueAt_of_sv hL hτ' fun z J hJ => ?_, fun a => ?_⟩
  · have q := sv_of_isValueAt (hw a) h hJ
    rw [MonObj.comp_one] at q
    rw [sv_pullS _ _ _ _ _ z hJ, ← Over.comp_left, lift_whiskerRight, Category.id_comp, q, k₂ _ _ z J hJ,
      Category.id_comp]
    exact congrArg (· * _) ((gs_pull (𝟙 _) h.left z ⊤ trivial _).trans (by rw [Category.id_comp])).symm
  · exact (congrArg h.left.appTop.hom (hv a)).trans (map_mul _ _ _)

theorem exists_basicOpen_isGenSec (hS : SecBaseChangeAnySt) [IsAffine T.left] (V : T.left.Opens) (p : T.left)
    (hp : p ∈ V) : ∃ f : Γ(T.left, ⊤), p ∈ T.left.basicOpen f ∧
      ∃ j : overRes (T.left.basicOpen f) ⟶ overRes V, j ≫ overResι V = overResι _ ∧
        ∀ th, IsGenSec P.A P.L 1 th → IsGenSec P.A P.L 1 (pullS P.A 1 j th) := by
  obtain ⟨V₀, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨f, hf, hpf⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := V ⊓ T.hom ⁻¹ᵁ V₀) ⟨p, hp, hV⟩ trivial
  let W := T.left.basicOpen f
  let l : overRes W ⟶ overRes (T := baseOver S) V₀ := Over.homMk
    (IsOpenImmersion.lift V₀.ι (W.ι ≫ T.hom) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact (hf y.2).2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  have hle : W ≤ V := hf.trans inf_le_left
  let j : overRes W ⟶ overRes V := Over.homMk (T.left.homOfLE hle) (by
    change T.left.homOfLE hle ≫ V.ι ≫ T.hom = W.ι ≫ T.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])
  have hj : j ≫ overResι V = overResι W := Over.OverMorphism.ext (T.left.homOfLE_ι hle)
  refine ⟨f, hpf, j, hj, fun th H s => ?_⟩
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have : IsAffine (overRes W).left := hW
  obtain ⟨c, hc⟩ := exists_basis P 1 b hb (overRes W) l
  obtain ⟨n, u, hu⟩ := EmbPull.exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))
  obtain ⟨r, hr⟩ := H (pullS P.A 1 (overResι V) (SecM.toSec P.A u))
  have hr' : pullM P.A P.L 1 (overResι V) u = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
  have e₁ := congrArg (pullM P.A P.L 1 j) hr'
  rw [pullM_comp _ P.isLB, hj, hu, LinearMap.map_smulₛₗ] at e₁
  obtain ⟨d, hd⟩ : ∃ d : Γ((overRes W).left, ⊤), SecM.ofSec P.A s =
      d • pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)) := by
    have := c.sum_repr (SecM.ofSec P.A s)
    rw [Fintype.sum_unique, hc] at this
    exact ⟨_, this.symm⟩
  have hf₁ : IsUnit (W.ι.appTop.hom f) := by
    refine W.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun y _ => ?_
    refine (Scheme.mem_basicOpen_top _ _ y).1 ?_
    rw [← Scheme.preimage_basicOpen_top]
    exact y.2
  obtain ⟨a, ha⟩ : IsUnit ((overResι W).left.appTop.hom (f ^ n)) := by
    rw [map_pow]
    exact hf₁.pow n
  have key : SecM.ofSec P.A s = (d * (a⁻¹ : Γ((overRes W).left, ⊤)ˣ) * j.left.appTop.hom r) •
      pullM P.A P.L 1 j (SecM.ofSec P.A th) := by
    rw [mul_smul, ← e₁, ← ha, ← mul_smul, Units.inv_mul_cancel_right, hd]
  exact ⟨_, fun i => congrArg (fun q => q.1 i) key⟩

theorem isThetaPt_pull (hS : SecBaseChangeAnySt) [IsAffine T.left] [IsAffine T'.left] (h : T' ⟶ T) {n : ℕ} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P n x v) :
    IsThetaPt P n (fun a => h ≫ x a) (fun a => h.left.appTop.hom (v a)) := by
  obtain ⟨h₁, h₂, H⟩ := H
  refine ⟨h₁, by simpa using h₂.map h.left.appTop.hom, fun p => ?_⟩
  obtain ⟨V, hV, H⟩ := H (h.left p)
  obtain ⟨f, hf, j, hj, hg⟩ := exists_basicOpen_isGenSec P hS V _ hV
  let f' := h.left.appTop.hom f
  have hf' : h.left ⁻¹ᵁ T.left.basicOpen f = T'.left.basicOpen f' := Scheme.preimage_basicOpen_top _ _
  let W := T.left.basicOpen f
  let W' := T'.left.basicOpen f'
  let k₀ : W'.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (W'.ι ≫ h.left) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact hf'.ge y.2)
  have hk₀ : k₀ ≫ W.ι = W'.ι ≫ h.left := IsOpenImmersion.lift_fac _ _ _
  let k : overRes W' ⟶ overRes W := Over.homMk k₀ (by
    change k₀ ≫ W.ι ≫ T.hom = W'.ι ≫ T'.hom
    rw [← Category.assoc, hk₀, Category.assoc, Over.w])
  have hk : k ≫ overResι W = overResι W' ≫ h := Over.OverMorphism.ext hk₀
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have hW' : IsAffineOpen W' := (isAffineOpen_top _).basicOpen f'
  have : IsAffine (overRes W).left := hW
  have : IsAffine (overRes W').left := hW'
  have Q := isThetaPtOver_pull_of_gen P (isThetaPtOver_pull_of_gen P H j hg) k
    fun _ => EmbPull.isGenSec_pullS P hS k
  have e : k ≫ j ≫ overResι V = overResι W' ≫ h := by rw [hj]; exact hk
  refine ⟨W', hf'.le hf, ?_⟩
  convert Q using 2 with a a
  · rw [← Category.assoc, ← e]
    simp only [Category.assoc]
  · exact (congrArg (fun q => q.left.appTop.hom (v a)) e).symm

end GlobalTheory.ThetaBaseChange

theorem GlobalTheory.hasTh_baseChange : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), t.HasTh x v → t.HasTh (spMap φ ≫ x) (fun a => φ (v a)) := by
  intro hl o _ g N' J b S s t R R' _ _ φ x v H
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap φ ≫ x)).left := inferInstanceAs (IsAffine (Spec _))
  have Q := GlobalTheory.ThetaBaseChange.isThetaPt_pull t.pol hl.secBaseChangeAny
    (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ x) ⟶ Over.mk x) H
  unfold TObj.HasTh
  convert Q using 2 with a a
  · exact Over.OverMorphism.ext (Category.assoc (spMap φ) x (t.lab a).left)
  · exact congrArg (fun q => q.hom (v a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicLiftRegularOfPeriodsZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.ZeroClass
open VertReg

section
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → ℂ}

theorem locDer_sub {V V' : X.Opens} {d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDer q p m D V d)
    (h' : LocDer q p m D V' d') : LocDer q p m (fun _ => 0) (V ⊓ V') (fun W f => d W f - d' W f) := by
  constructor
  · intro W hW f f'
    rw [h.add W (hW.trans inf_le_left), h'.add W (hW.trans inf_le_right)]
    abel
  · intro W hW f f'
    rw [h.mul W (hW.trans inf_le_left), h'.mul W (hW.trans inf_le_right)]
    ring
  · intro W W' hle hW f
    rw [h.res W W' hle (hW.trans inf_le_left), h'.res W W' hle (hW.trans inf_le_right), map_sub]
  · intro W hW r
    rw [h.base W (hW.trans inf_le_left), h'.base W (hW.trans inf_le_right), sub_self,
      ← liftConstHom_apply, map_zero]

theorem ptOf_of_le {V : X.Opens} {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDer q p m D V d)
    (y : Sp ℂ ⟶ Y) {W : X.Opens} (hW : W ≤ V) (hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W) (f : Γ(X, W)) :
    ptOf V d y W f = valAt' y (m ⁻¹ᵁ W) (d W f) := by
  have hy' : ⊤ ≤ (y ≫ m) ⁻¹ᵁ (W ⊓ V) := (inf_eq_left.mpr hW).symm ▸ hy
  exact val_res h y inf_le_left hW hy' f

theorem ptDer_sub {y : Sp ℂ ⟶ X} {δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W f => δ W f - δ' W f) := by
  constructor
  · intro W hW f f'
    simp only [h.add W hW, h'.add W hW]
    ring
  · intro W hW f f'
    simp only [h.mul W hW, h'.mul W hW]
    ring
  · intro W W' hle hW f
    simp only [h.res W W' hle hW, h'.res W W' hle hW]

end

theorem ex_add_lattice {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)
    (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).mpr l.2, ← (u.ker 0).mpr (zero_mem _), ← u.ex_add, add_zero]

variable {P₀ : Out.PolAV (Sp ℂ)} {u : HolUnif P₀.A P₀.L P₀.g} {Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ} {χ : u.Λ → ℂ}
  {R : Type} [CommRing R] {x₀ : R →+* ℂ} {X : Scheme.{0}} {p : X ⟶ Sp R} {m : P₀.A.left ⟶ X}

theorem vector_ext (hu : GoodU u Hm χ) (hp : Smooth p) (hm : IsPullback m P₀.A.hom p (spMap x₀)) {V : X.Opens}
    {z : Fin P₀.g → ℂ} (hz : z ∈ dom u m V) {v v' : Fin P₀.g → ℂ}
    (h : ∀ W, W ≤ V → z ∈ dom u m W → ∀ f, fderiv ℂ (fn u m W f) z v = fderiv ℂ (fn u m W f) z v') : v = v' := by
  obtain ⟨W, t, hzW, hdet⟩ := exists_fibre_coords P₀ u Hm χ hu R x₀ X p m hp hm z
  have hzWV : z ∈ dom u m (W ⊓ V) := fun a ha => ⟨hzW ha, hz ha⟩
  have hlin : ∀ (w : Fin P₀.g → ℂ) b, fderiv ℂ (fn u m W (t b)) z w =
      Matrix.vecMul w (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)) b := by
    intro w b
    conv_lhs => rw [← Finset.univ_sum_single w]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show Pi.single a (w a) = w a • (Pi.single a 1 : Fin P₀.g → ℂ) by
      ext j; by_cases hj : j = a <;> simp [hj], map_smul, smul_eq_mul]
  have hk : Matrix.vecMul (v - v') (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)) = 0 := by
    ext b
    rw [← hlin, map_sub, Pi.zero_apply, sub_eq_zero]
    have e := h (W ⊓ V) inf_le_right hzWV (resG X inf_le_left (t b))
    rwa [fderiv_fn_resG u m inf_le_left (t b) hzWV] at e
  exact sub_eq_zero.mp (Matrix.eq_zero_of_vecMul_eq_zero hdet hk)

theorem exists_periodic_vector (hu : GoodU u Hm χ) (hp : Smooth p) (hm : IsPullback m P₀.A.hom p (spMap x₀))
    {D : R → ℂ} {s} (hs : KSRel u p m D 0 s) {V : X.Opens} {d} (hd : LocDer P₀.A.hom p m D V d) :
    ∃ w : (Fin P₀.g → ℂ) → (Fin P₀.g → ℂ), DifferentiableOn ℂ w (dom u m V) ∧
      (∀ (l : u.Λ), ∀ z ∈ dom u m V, w (z + l) = w z) ∧
      ∀ W, W ≤ V → ∀ f, ∀ z ∈ dom u m W,
        s z W f = valAt' (u.ex z).left (m ⁻¹ᵁ W) (d W f) + fderiv ℂ (fn u m W f) z (w z) := by
  have hq : ∀ z, (u.ex z).left ≫ P₀.A.hom = 𝟙 _ := fun z => by simp
  have hex : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => ex_add_lattice u z l
  have hdomV : IsOpen (dom u m V) := (u.hol (m ⁻¹ᵁ V) 0).1
  have hpt : ∀ z ∈ dom u m V, PtDer ((u.ex z).left ≫ m)
      (fun W f => s z W f - ptOf V d (u.ex z).left W f) ∧
      ∀ r, s z ⊤ (constFn p ⊤ r) - ptOf V d (u.ex z).left ⊤ (constFn p ⊤ r) = 0 := fun z hz =>
    ⟨ptDer_sub (hs.der z) (ptDer_ptOf hd (u.ex z).left hz), fun r => by
      rw [hs.base z r, ptOf_const hd (u.ex z).left (hq z) hz r, sub_self]⟩
  obtain ⟨w, hw, hrep⟩ := _root_.GlobalTheory.KS.VertField.exists_differentiableOn_vertical P₀ u Hm χ hu R x₀ X p m hp hm P₀.g (dom u m V) id
    (fun z W f => s z W f - ptOf V d (u.ex z).left W f) hdomV differentiable_id hpt
    (by
      intro W f
      apply DifferentiableOn.sub
      · exact (hs.hol W f).mono fun _ hz => hz.2
      · exact (u.hol (m ⁻¹ᵁ (W ⊓ V)) (d (W ⊓ V) (resG X inf_le_left f))).2.mono
          fun _ hz a ha => ⟨hz.2 ha, hz.1 ha⟩)
  refine ⟨w, hw, fun l z hz => ?_, fun W hWV f z hz => ?_⟩
  · have hzl : z + l ∈ dom u m V := by
      show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ V
      rw [hex]; exact hz
    have hfn : ∀ W (f : Γ(X, W)), fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fn u m W f) z := by
      intro W f
      have e : (fun x => fn u m W f (x + l)) = fn u m W f := by
        funext x; simp only [fn, hex]
      rw [← fderiv_comp_add_right, e]
    refine ((_root_.GlobalTheory.KS.VertFamily.existsUnique_vector P₀ u Hm χ hu R x₀ X p m hp hm z _ (hpt z hz).1 (hpt z hz).2).unique
      (fun W f hzW => ?_) (fun W f hzW => ?_))
    · have hzlW : z + l ∈ dom u m W := by
        show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ W
        rw [hex]; exact hzW
      have e := hrep (z + l) hzl W f hzlW
      simp only [id, hex, hfn] at e
      rw [← e, hs.per l W f z hzW, Matrix.zero_mulVec, map_zero, add_zero]
    · exact hrep z hz W f hzW
  · have e := hrep z (fun a ha => hWV (hz ha)) W f hz
    rw [ptOf_of_le hd (u.ex z).left hWV hz f] at e
    simp only [id] at e
    rw [← e]; ring

private theorem valAt'_sub' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valAt' x U (a - b) = valAt' x U a - valAt' x U b := by
  simp only [valAt', dif_pos hx, valAt, map_sub]

private theorem valAt'_add_of_top_le {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valAt' x U (a + b) = valAt' x U a + valAt' x U b := by
  simp only [valAt', dif_pos hx, valAt, map_add (f := _)]

private theorem valAt'_mul_of_top_le {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valAt' x U (a * b) = valAt' x U a * valAt' x U b := by
  simp only [valAt', dif_pos hx, valAt, map_mul]

private theorem valAt'_finset_sum {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    {κ : Type} (s : Finset κ) (F : κ → Γ(X, U)) : valAt' x U (∑ i ∈ s, F i) = ∑ i ∈ s, valAt' x U (F i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [valAt', dif_pos hx, valAt, map_sum]

private theorem valAt'_comp' {Y X : Scheme.{0}} (y : Sp ℂ ⟶ Y) (m : Y ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    valAt' (y ≫ m) W f = valAt' y (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  by_cases hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W
  · have hy' : ⊤ ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W) := hy
    rw [valAt', dif_pos hy, valAt', dif_pos hy', valAt, valAt]
    first
      | (rw [Scheme.comp_appLE]; rfl)
      | simp [Scheme.comp_appLE]
      | simp [Scheme.Hom.comp_appLE]
  · have hy' : ¬ ⊤ ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W) := hy
    rw [valAt', dite_eq_right hy, valAt', dite_eq_right hy']

private theorem valAt'_resG_of_top_le {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (hx : ⊤ ≤ x ⁻¹ᵁ V)
    (a : Γ(X, U)) : valAt' x V (resG X h a) = valAt' x U a := by
  have hx' : ⊤ ≤ x ⁻¹ᵁ U := fun p hp => h (hx hp)
  rw [valAt', dif_pos hx, valAt', dif_pos hx', valAt, valAt, resG]
  congr 1
  exact congrArg (fun φ => φ.hom a) (x.map_appLE hx (homOfLE h).op)

private theorem continuousLinearMap_apply_eq_sum_single {n : ℕ} (φ : (Fin n → ℂ) →L[ℂ] ℂ) (w : Fin n → ℂ) :
    φ w = ∑ b, w b * φ (Pi.single b 1) := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show Pi.single a (w a) = w a • (Pi.single a 1 : Fin n → ℂ) by
    ext j; by_cases hj : j = a <;> simp [hj], map_smul, smul_eq_mul]

end GlobalTheory.KS.ZeroClass

namespace GlobalTheory.KS
open ZeroClass

theorem regular_of_periods_zero : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∀ W₀, IsAffineOpen W₀ → ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), ∃ a : Γ(P₀.A.left, m ⁻¹ᵁ W), ∀ z ∈ dom u m W, valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f := by
  intro hL P₀ u Hm χ hu R _ x₀ X p m hp hm D s hD hs W₀ hW₀ W hWW₀ f
  choose dd hdd using fun i : X.affineOpens =>
    exists_locDer_of_smooth R x₀ P₀.A.left X P₀.A.hom p m D i.1 hp hm.w hD i.2
  choose ww hww hper hrep using fun i : X.affineOpens => exists_periodic_vector hu hp hm hs (hdd i)
  choose cc hcc using fun i j : X.affineOpens =>
    locDer_regular_coeff P₀ u Hm χ hu R x₀ X p m hp hm _ _ (locDer_sub (hdd i) (hdd j))
  have hrel : ∀ (i j : X.affineOpens) z, z ∈ dom u m (i.1 ⊓ j.1) →
      ww j z - ww i z = fun a => valAt' (u.ex z).left (m ⁻¹ᵁ (i.1 ⊓ j.1)) (cc i j a) := by
    intro i j z hz
    refine vector_ext hu hp hm hz fun W' hW' hzW' f' => ?_
    have e1 := hrep i W' (hW'.trans inf_le_left) f' z hzW'
    have e2 := hrep j W' (hW'.trans inf_le_right) f' z hzW'
    have e3 := hcc i j W' hW' f' z hzW'
    rw [valAt'_sub' (u.ex z).left (m ⁻¹ᵁ W') hzW'] at e3
    rw [map_sub, ← e3]
    linear_combination e1 - e2
  have hcov : ⨆ i : X.affineOpens, m ⁻¹ᵁ i.1 = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    have hy : m.base y ∈ (⨆ i : X.affineOpens, (i.1 : X.Opens)) := by
      rw [iSup_affineOpens_eq_top X]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let i₀ : X.affineOpens := ⟨W₀, hW₀⟩
  have hcob : ∀ a : Fin P₀.g, ∃ e : Γ(P₀.A.left, m ⁻¹ᵁ W₀), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W₀) →
      valAt' (u.ex z).left (m ⁻¹ᵁ W₀) e = ww i₀ z a := fun a =>
    algebraic_coboundary_of_holomorphic_coboundary hL P₀ u Hm χ hu X.affineOpens (fun i => m ⁻¹ᵁ i.1)
      (fun i j => cc i j a) (fun i z => ww i z a) hcov
      (fun i => ⟨(differentiableOn_pi.mp (hww i)) a, fun l z hz => congrFun (hper i l z hz) a⟩)
      (fun i j z hz => (congrFun (hrel i j z hz) a).symm) i₀
  choose ee hee using hcob
  choose δ hδ hδv using fun b : Fin P₀.g => invariant_field_algebraic P₀ u Hm χ hu (Pi.single b 1)
  have hW' : m ⁻¹ᵁ W ≤ m ⁻¹ᵁ W₀ := fun y hy => hWW₀ hy
  refine ⟨dd i₀ W f + ∑ b, resG P₀.A.left hW' (ee b) *
    (show Γ(P₀.A.left, m ⁻¹ᵁ W) from δ b (m ⁻¹ᵁ W) ((m.app W).hom f)), fun z hz => ?_⟩
  have hz0 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W₀) := fun y hy => hWW₀ (hz hy)
  have hzW : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) := hz
  rw [hrep i₀ W hWW₀ f z hz, valAt'_add_of_top_le _ _ hzW, valAt'_finset_sum _ _ hzW]
  congr 1
  rw [continuousLinearMap_apply_eq_sum_single (fderiv ℂ (fn u m W f) z) (ww i₀ z)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hv : valAt' (u.ex z).left (m ⁻¹ᵁ W) (show Γ(P₀.A.left, m ⁻¹ᵁ W) from δ b (m ⁻¹ᵁ W) ((m.app W).hom f)) =
      fderiv ℂ (fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f)) z (Pi.single b 1) :=
    hδv b (m ⁻¹ᵁ W) ((m.app W).hom f) z hzW
  have efn : (fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f)) = fn u m W f :=
    funext fun z' => (valAt'_comp' _ _ _ _).symm
  rw [valAt'_mul_of_top_le _ _ hzW, valAt'_resG_of_top_le _ hW' hzW, hee b z hz0, hv, efn]

end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitutionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.lineBundleIso_linComb_symm_biadditive_substitution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Pb : LB (G2 A).left), Pb.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso Pb (Pb.pull (lift (snd A A) (fst A A)).left) → ∀ (T : Over S) (n m : ℕ) (x : Fin n → (T ⟶ A)) (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ), W' + W'.transpose = c.transpose * (W + W.transpose) * c → LBIso (LB.LinComb Pb (K := Fin n × Fin n) (fun uv => (lift (x uv.1) (x uv.2)).left) (fun uv => W' uv.1 uv.2)) (LB.LinComb Pb (K := Fin m × Fin m) (fun uv => (lift (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i)).left) (fun uv => W uv.1 uv.2)) := by
  first | exact @GlobalTheory.BilinCalc.main | exact GlobalTheory.BilinCalc.main | (intros; apply GlobalTheory.BilinCalc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem obj_pull :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f) :=
  ObjPull.objPull_of_lie_of_ample LiePull.lieMult_pull
    (PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SabMapEqOfLevelEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.sabMap_eq_of_level_eq : Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ :=
  GlobalTheory.obj_rigid_of_laws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemistableReductionSplitOfPadic
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SS

theorem semistablePol_of_padic : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.SS.SemistablePol := by
  intro H V K _ _ _ _ _ _ _ _ hfin A
  obtain ⟨p, hp, K₀, e, e₀, hK₀, he⟩ := GlobalTheory.completeDVR_eq_integralClosure_padicInt.1 V K hfin
  obtain ⟨P, ψ, hψ⟩ : ∃ (P : PolAV (Sp K₀)) (ψ : P.A.left ⟶ A.A.left),
      IsGrpPullback P.A A.A (spMap e.toRingHom) ψ := by
    obtain ⟨P', g, hg, -, hm, -⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap e.toRingHom) A
    refine ⟨P', g, hg, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hg.w y), ← hm]
    rfl
  obtain ⟨K', h, hloc, hK', G, gG, hG, hE, φ, hφ⟩ :=
    GlobalTheory.exists_semiAbelian_model_split_specialFibre H p K₀ P
  obtain ⟨hdvr, hfr, hc, f, hf, hlf, hfx⟩ := GlobalTheory.completeDVR_eq_integralClosure_padicInt.2 p K₀ K' h hK'
  letI aV : Algebra V (integralClosure ℤ_[p] K') := (f.comp e₀.toRingHom).toAlgebra
  letI aK : Algebra K K' := ((IntermediateField.inclusion h).toRingHom.comp e.toRingHom).toAlgebra
  refine ⟨integralClosure ℤ_[p] K', K', inferInstance, inferInstance, hdvr, inferInstance, aV, inferInstance, aK, hfr,
    ?_, ?_, ?_, hc, G, gG, ?_, hG, hE⟩
  · ext1 x
    change ((f (e₀ x) : integralClosure ℤ_[p] K') : K') = IntermediateField.inclusion h (e (algebraMap V K x))
    rw [hfx, he]
  · exact RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ e₀.surjective)
  · haveI : IsLocalHom e₀.toRingHom := isLocalHom_of_leftInverse e₀.symm.toRingHom e₀.left_inv
    exact RingHom.isLocalHom_comp f e₀.toRingHom
  · obtain ⟨i, hi, -⟩ := grpPullback_iso
      ((hφ.comp hψ).congr (GlobalTheory.SplitReduction.spMap_comp _ _) rfl)
      (isGrpPullback_pullback A.A (spMap (algebraMap K K')))
    exact ⟨i, hi⟩

end GlobalTheory.SS
end

