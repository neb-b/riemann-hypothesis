module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.AnForm.R (ds_stalkId_eq_map mem_support_iff_stalkId)
open ReciprocityTheory.AnForm.R.FinalTheorems (stalkId)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open GlobalTheory.TopForm (le_preimage_inf)
open GlobalTheory.Adelic (cutIdeal ideal_cutIdeal mem_support_cutIdeal)
open H0

variable {k : Type} [CommRing k] {Y T : Scheme.{0}}

theorem exists_affine {U : Y.Opens} {y : Y} (hy : y ∈ U) :
    ∃ W : Y.affineOpens, y ∈ W.1 ∧ W.1 ≤ U :=
  let ⟨W, hW, h₁, h₂⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hy
  ⟨⟨W, hW⟩, h₁, h₂⟩

variable (I : Y.IdealSheafData)

theorem stalkId_pow (a : ℕ) (y : Y) : stalkId (I ^ a) y = stalkId I y ^ a := by
  obtain ⟨W, hW, -⟩ := exists_affine (U := ⊤) (y := y) trivial
  rw [ds_stalkId_eq_map _ W y hW, ds_stalkId_eq_map _ W y hW, ← Ideal.map_pow]
  rfl

theorem stalkId_eq_top {y : Y} (hy : y ∉ I.support) : stalkId I y = ⊤ :=
  not_not.1 fun h => hy ((mem_support_iff_stalkId I y).2 h)

theorem ι_mem_support (z : I.subscheme) : I.subschemeι z ∈ I.support :=
  I.range_subschemeι.le ⟨z, rfl⟩


variable {I} in
theorem exists_ι_eq {y : Y} (hy : y ∈ I.support) : ∃ z : I.subscheme, I.subschemeι z = y :=
  I.range_subschemeι.ge hy

theorem ker_stalkMap (z : I.subscheme) :
    RingHom.ker (I.subschemeι.stalkMap z).hom = stalkId I (I.subschemeι z) := by
  have key (W : Y.affineOpens) (hW : I.subschemeι z ∈ W.1) (a : Γ(Y, W.1)) :
      (I.subschemeι.stalkMap z).hom (ger _ hW a) =
        ger (U := I.subschemeι ⁻¹ᵁ W.1) z hW ((I.subschemeι.app W.1).hom a) :=
    Scheme.Hom.germ_stalkMap_apply _ _ z hW a
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨U, hU, a, rfl⟩ := Y.presheaf.germ_exist x
    have h₀ : ger (U := I.subschemeι ⁻¹ᵁ U) z hU ((I.subschemeι.app U).hom a) =
        ger (U := I.subschemeι ⁻¹ᵁ U) z hU 0 :=
      (Scheme.Hom.germ_stalkMap_apply _ _ z hU a).symm.trans (hx.trans (map_zero _).symm)
    obtain ⟨V, hV, i₁, i₂, e⟩ := I.subscheme.presheaf.germ_eq z hU hU _ _ h₀
    obtain ⟨V', hV', hVV⟩ := I.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.1 V.2
    obtain ⟨W, hW, hle⟩ := exists_affine (U := U ⊓ ⟨V', hV'⟩) (y := I.subschemeι z)
      ⟨hU, hVV.ge hV⟩
    have hWV : I.subschemeι ⁻¹ᵁ W.1 ≤ V := fun w hw => hVV.le (hle hw).2
    have hm : resG Y (hle.trans inf_le_left) a ∈ I.ideal W := by
      rw [← I.ker_subschemeι_app W, RingHom.mem_ker, Scheme.Hom.app_eq_appLE, LB.appLE_resG,
        ← resG_app, ← resG_resG i₁.le hWV]
      exact (congrArg (resG _ hWV) (e.trans (map_zero _))).trans (map_zero _)
    rw [ds_stalkId_eq_map I W _ hW]
    exact ger_resG (hle.trans inf_le_left) _ hW a ▸ Ideal.mem_map_of_mem _ hm
  · obtain ⟨W, hW, -⟩ := exists_affine (U := ⊤) (y := I.subschemeι z) trivial
    rw [ds_stalkId_eq_map I W _ hW, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [← I.ker_subschemeι_app W, RingHom.mem_ker] at ha
    exact (key W hW a).trans ((congrArg _ ha).trans (map_zero _))

theorem mem_ideal_iff_ger (W : Y.affineOpens) (a : Γ(Y, W.1)) :
    a ∈ I.ideal W ↔ ∀ y hy, ger y hy a ∈ stalkId I y := by
  refine ⟨fun h y hy => ds_stalkId_eq_map I W y hy ▸ Ideal.mem_map_of_mem _ h, fun h => ?_⟩
  rw [← I.ker_subschemeι_app W, RingHom.mem_ker]
  refine fun_ext_ger fun z hz => ?_
  have := (ker_stalkMap I z).ge (h _ hz)
  exact (Scheme.Hom.germ_stalkMap_apply _ _ z hz a).symm.trans (this.trans (map_zero _).symm)

variable {L : LB Y} (hL : L.IsLB) {ι : Type} (s : ι → L.Sec)

abbrev secGer (j : L.ι) (y : Y) (hj : y ∈ L.U j) : ι → Y.presheaf.stalk y :=
  fun i => ger y hj ((s i).f j)

theorem stalkId_cutIdeal (j : L.ι) (y : Y) (hj : y ∈ L.U j) :
    stalkId (cutIdeal hL s) y = Ideal.span (Set.range (secGer s j y hj)) := by
  obtain ⟨W, hW, hle⟩ := exists_affine hj
  rw [ds_stalkId_eq_map _ W y hW, ideal_cutIdeal hL s W j hle, Ideal.map_span, ← Set.range_comp]
  exact congrArg (fun f => Ideal.span (Set.range f)) (funext fun i => ger_resG hle y hW _)

theorem vanishesAlong_cutIdeal (i : ι) : VanishesAlong (s i) (cutIdeal hL s).subschemeι :=
  fun j => fun_ext_ger fun z hz => by
    have : ger (U := L.U j) ((cutIdeal hL s).subschemeι z) hz ((s i).f j) ∈ RingHom.ker ((cutIdeal hL s).subschemeι.stalkMap z).hom := by
      rw [ker_stalkMap, stalkId_cutIdeal hL s j _ hz]
      exact Ideal.subset_span ⟨i, rfl⟩
    exact (Scheme.Hom.germ_stalkMap_apply _ _ z hz _).symm.trans (this.trans (map_zero _).symm)

theorem secGer_change (j j' : L.ι) (y : Y) (hj : y ∈ L.U j) (hj' : y ∈ L.U j') (i : ι) :
    secGer s j y hj i = tr L y j j' * secGer s j' y hj' i := by
  have e := congrArg (ger y (memInf hj hj')) (sec_rel (s i) j j' inf_le_left inf_le_right le_rfl)
  rwa [map_mul, ger_resG, ger_resG, ger_resG, ← val_tr] at e

section Etale

variable {p : Y ⟶ Sp k}

theorem formallyUnramified_quotient (h : FormallyUnramified (I.subschemeι ≫ p)) (W : Y.affineOpens) :
    ((Ideal.Quotient.mk (I.ideal W)).comp (algX p W.1)).FormallyUnramified := by
  have h₁ := HasRingHomProperty.appLE @FormallyUnramified (I.subschemeι ≫ p) h
    ⟨⊤, isAffineOpen_top _⟩ ⟨_, W.2.preimage I.subschemeι⟩ le_top
  have h₂ := RingHom.FormallyUnramified.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv h₁
  let e : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W.1) ≃+* Γ(Y, W.1) ⧸ I.ideal W :=
    (RingHom.quotientKerEquivOfSurjective (I.subschemeι_app_surjective W)).symm.trans
      (Ideal.quotEquivOfEq (I.ker_subschemeι_app W))
  have h₃ := RingHom.FormallyUnramified.respectsIso.1 _ e h₂
  have e₁ := Scheme.Hom.appLE_comp_appLE I.subschemeι p ⊤ W.1 (I.subschemeι ⁻¹ᵁ W.1) le_top le_rfl
  have e₂ (a : Γ(Y, W.1)) : e ((I.subschemeι.app W.1).hom a) = Ideal.Quotient.mk _ a := by
    rw [RingEquiv.trans_apply, ← RingHom.quotientKerEquivOfSurjective_apply_mk
      (I.subschemeι_app_surjective W), RingEquiv.symm_apply_apply]
    rfl
  rw [Scheme.Hom.appLE_eq_app] at e₁
  refine (congrArg RingHom.FormallyUnramified (RingHom.ext fun c => ?_)).mp h₃
  exact (congrArg e (congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
    e₁).symm).trans (e₂ _)

variable {D : ℕ} [SmoothOfRelativeDimension D p] (K : CanonLB p D) (s : Fin D → L.Sec)

theorem isUnit_ger_jacFun (h : FormallyUnramified ((cutIdeal hL s).subschemeι ≫ p)) {y : Y}
    (hy : y ∈ (cutIdeal hL s).support) (i : K.bundle.ι) (j : L.ι)
    (hij : y ∈ K.bundle.U i ⊓ L.U j) : IsUnit (ger y hij (K.jacFun s i j)) := by
  obtain ⟨z, rfl⟩ := exists_ι_eq hy
  obtain ⟨W, hW, hle⟩ := exists_affine hij
  have hu := formallyUnramified_quotient _ h W
  rw [ideal_cutIdeal hL s W j (hle.trans inf_le_right)] at hu
  have := K.isUnit_map_jacobian i W.2 (hle.trans inf_le_left) _ hu
    (((cutIdeal hL s).subschemeι.stalkMap z).hom.comp (ger _ hW)) fun a => by
      rw [RingHom.comp_apply, ger_resG, ← RingHom.mem_ker, ker_stalkMap,
        stalkId_cutIdeal hL s j _ hij.2]
      exact Ideal.subset_span ⟨a, rfl⟩
  rw [← K.resG_jacFun s i j hle, RingHom.comp_apply, ger_resG] at this
  exact IsUnit.of_map _ _ this

theorem isQuasiRegularSeq_of_isFreeGen {A : Type} [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) (x : Fin D → A)
    (hx : TopForm.IsFreeGen A (TopForm.dForm α x)) : IsQuasiRegularSeq A x := by
  let := α.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  cases subsingleton_or_nontrivial A with
  | inl _ => exact isQuasiRegularSeq_of_smul_top_eq_top (Subsingleton.elim _ _)
  | inr _ =>
    have := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D (R := k) (S := A)
    have hr : Module.finrank A Ω[A⁄k] = D := Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := A) D)
    let b := Module.finBasisOfFinrankEq A Ω[A⁄k] hr
    let v : Fin D → Ω[A⁄k] := fun i => KaehlerDifferential.D k A (x i)
    have e := alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti A D)
      (Matrix.of fun i j => b.repr (v i) j) b
    simp only [Matrix.of_apply, b.sum_repr] at e
    have hu := (TopForm.isFreeGen_ιMulti b).smul_iff.1 ((congrArg (TopForm.IsFreeGen A) e).mp hx)
    rw [← Matrix.det_transpose] at hu
    obtain ⟨h₁, h₂⟩ := (b.is_basis_iff_det (v := v)).2 hu
    let := (MvPolynomial.eval₂Hom α x).toAlgebra
    have : IsScalarTower k (MvPolynomial (Fin D) k) A :=
      IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C α x r).symm
    have hX (i) : algebraMap (MvPolynomial (Fin D) k) A (MvPolynomial.X i) = x i :=
      MvPolynomial.eval₂Hom_X' α x i
    have := EtaleCoordJacobian.etale_of_basis k A (Fin D) (Module.Basis.mk h₁ h₂.ge)
      fun i => by rw [Module.Basis.mk_apply, hX]
    simpa only [hX] using (isQuasiRegularSeq_X (R := k) (Fin D)).of_flat A


omit K in
theorem isQuasiRegularSeq_secGer (h : FormallyUnramified ((cutIdeal hL s).subschemeι ≫ p)) {y : Y}
    (hy : y ∈ (cutIdeal hL s).support) (j : L.ι) (hj : y ∈ L.U j) :
    IsQuasiRegularSeq (Y.presheaf.stalk y) (secGer s j y hj) := by
  let K := CanonLB.all p D
  obtain ⟨i, hi⟩ := exists_chart K.isLB y
  have hb : y ∈ Y.basicOpen (K.jacFun s i j) :=
    (Y.mem_basicOpen _ y (memInf hi hj)).2 (isUnit_ger_jacFun hL K s h hy i j _)
  obtain ⟨⟨V, hV⟩, hx, hle⟩ := exists_affine hb
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨σ, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (σ : Set Γ(Y, V)), y ∈ Y.basicOpen (t : Γ(Y, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← TopForm.resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  have hW := IsAffineOpen.basicOpen hV (t : Γ(Y, V))
  have l₁ := (Y.basicOpen_le (t : Γ(Y, V))).trans hle
  have l₂ := l₁.trans (Y.basicOpen_le _)
  have hu : IsUnit (resG Y l₂ (K.jacFun s i j)) :=
    resG_resG (Y.basicOpen_le _) l₁ (K.jacFun s i j) ▸
      (Y.toRingedSpace.isUnit_res_basicOpen (K.jacFun s i j)).map (resG Y l₁)
  rw [K.resG_jacFun, K.isUnit_jacobian_iff i hW] at hu
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hxt⟩ : Y.basicOpen (t : Γ(Y, V)))
  have := hW.isLocalization_stalk ⟨y, hxt⟩
  have hq := (isQuasiRegularSeq_of_isFreeGen h₂ _ hu.gen).of_isLocalization (Y.presheaf.stalk y)
    (hW.primeIdealOf ⟨y, hxt⟩).asIdeal.primeCompl
  exact (congrArg _ (funext fun a => ger_resG (l₂.trans inf_le_right) y hxt _)).mp hq

end Etale

end GlobalTheory.Vanishing
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

abbrev Mt (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def frDom (Hm : Mt n) (q : ℕ) : Set (Mt n) :=
  {x | x.det ≠ 0 ∧ ∀ i : Fin (n + 1),
    0 < ReciprocityTheory.ChartRestriction.G.FD.psgn q i * (ReciprocityTheory.ChartRestriction.G.FD.lminor (-(xᴴ * Hm * x)) i).re}

def UpT (b : Mt n) : Prop := b.det ≠ 0 ∧ ∀ a c : Fin n, c < a → b a c = 0

def OrthFr (Hm : Mt n) (q : ℕ) (x₀ : Mt n) : Prop :=
  q ≤ n ∧ x₀ᴴ * Hm * x₀ = diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)

def UG (Hm : ι → Mt n) : Set (ι → Mt n) := {u | ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (Hm τ)}

def frDoms (Hm : ι → Mt n) (q : ι → ℕ) : Set (ι → Fin n → Fin n → ℂ) := {x | ∀ τ, Matrix.of (x τ) ∈ frDom (Hm τ) (q τ)}

def HolSec (Hm : ι → Mt n) (q : ι → ℕ) (w : ι → Fin n → ℤ) (P : (ι → Fin n → Fin n → ℂ) → ℂ) : Prop :=
  DifferentiableOn ℂ P (frDoms Hm q) ∧
    ∀ x ∈ frDoms Hm q, ∀ b : ι → Mt n, (∀ τ, UpT (b τ)) →
      P (fun τ => (Matrix.of (x τ) * b τ : Mt n)) = (∏ τ, ∏ a, b τ a a ^ w τ a) * P x

def HolFn (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ) (f : (ι → Mt n) → ℂ) : Prop :=
  ∃ P, HolSec Hm q w P ∧ ∀ u ∈ UG Hm, f u = P fun τ => (u τ * x₀ τ : Mt n)

def lieH (Hm : Mt n) : Set (Mt n) := {X | Xᴴ * Hm + Hm * X = 0}

def SmFn (Hm : ι → Mt n) (f : (ι → Mt n) → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → ι) (Xs : Fin k → Mt n), (∀ i, Xs i ∈ lieH (Hm (τs i))) → ∀ u ∈ UG Hm,
    ContDiff ℝ ∞ fun t : Fin k → ℝ =>
      f (u * (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod)

def der (τ : ι) (X : Mt n) (f : (ι → Mt n) → ℂ) (u : ι → Mt n) : ℂ :=
  deriv (fun t : ℝ => f (u * (Pi.mulSingle τ (NormedSpace.exp (t • X)) : ι → Mt n))) 0

def conjH (Hm Z : Mt n) : Mt n := -(Hm⁻¹ * Zᴴ * Hm)

def derC (Hm : ι → Mt n) (τ : ι) (Z : Mt n) (f : (ι → Mt n) → ℂ) (u : ι → Mt n) : ℂ :=
  der τ ((1 / 2 : ℂ) • (Z + conjH (Hm τ) Z)) f u + Complex.I * der τ ((1 / (2 * Complex.I)) • (Z - conjH (Hm τ) Z)) f u

def KilledFn (Hm : ι → Mt n) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ) (f : (ι → Mt n) → ℂ) : Prop :=
  ∀ τ (a c : Fin n), a ≤ c → ∀ u ∈ UG Hm,
    derC Hm τ (x₀ τ * Matrix.single a c 1 * (x₀ τ)⁻¹) f u = if a = c then (w τ a : ℂ) * f u else 0

def torEl (x₀ : ι → Mt n) (s : ι → Fin n → ℝ) : ι → Mt n :=
  fun τ => x₀ τ * diagonal (fun a => Complex.exp ((s τ a : ℂ) * Complex.I)) * (x₀ τ)⁻¹

def torCh (w : ι → Fin n → ℤ) (s : ι → Fin n → ℝ) : ℂ := ∏ τ, ∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a

def dRepC {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Hm : Mt n) (σ : Mt n → (H →L[ℂ] H)) (Z : Mt n) (v : H) : H :=
  dRep σ ((1 / 2 : ℂ) • (Z + conjH Hm Z)) v + Complex.I • dRep σ ((1 / (2 * Complex.I)) • (Z - conjH Hm Z)) v

def gelfRep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Hm : Mt n) (σ : Mt n → (H →L[ℂ] H)) (k : ℕ) (v : H) : H :=
  ∑ idx : Fin (k + 1) → Fin n,
    (List.ofFn fun a : Fin (k + 1) => dRepC Hm σ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) v

def InZe (Hm : Mt n) (e : Fin n → ℂ) (m : Mt n) : Prop :=
  ∃ s : ℝ, m = 1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm)

end Local

section Adelic

variable {D : D7}

def HolShape {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Prop :=
  ∀ τ, Formalism.QuantumDeterminants.IsHCParam (M.lam τ) ∧ ∃ p ≤ V.rank, ∀ a, M.ε τ a = decide ((a : ℕ) < p)

def WtIs {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) : Prop :=
  ∀ τ c, (w τ c : ℝ) = extWt M τ (arr (nNeg (M.ε τ)) c)


open Classical in
def HolAd (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    (φ : GA D V → ℂ) : Prop :=
  ∀ g, ∃ f, HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w f ∧
    ∀ u ∈ GinfC V, φ (g * u) = f fun τ => archM V (θ τ) u

def ZI (V : HSp D) (ξ : Fin V.rank → D.host.E) : Subgroup (GA D V) :=
  Subgroup.closure {g | ∃ a : AF D.host.F ⊗[D.host.F] D.host.E,
    ((matHom V g).1 - 1 : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) =
      a • (vecMulVec ξ ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* V.gram)).map (incA D)}

def IsoVec (V : HSp D) (ξ : Fin V.rank → D.host.E) : Prop :=
  ξ ≠ 0 ∧ (fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ⬝ᵥ V.gram.mulVec ξ = 0

def ZCusp (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ ξ, IsoVec V ξ → ∀ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure →
    IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ → ∀ g, ∫ z in 𝓕, φ ((z : GA D V) * g) ∂μ = 0

structure HolForm (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (φ : GA D V → ℂ) : Prop where
  aut : IsAutFun V φ
  bdd : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C
  lev : ∀ k ∈ J, ∀ g, φ (g * k) = χ k * φ g
  hol : HolAd θ M w φ

structure FinPair (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop where
  haar : μ.IsHaarMeasure
  right : μ.IsMulRightInvariant
  fd : IsFundamentalDomain (GQ V) 𝓕 μ
  fin : μ 𝓕 ≠ ⊤

def nuQ (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Measure (AutQ V) := (μ.restrict 𝓕).map (autMk V)

def Repr (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (F : Lp ℂ 2 (nuQ V μ 𝓕)) (ψ : GA D V → ℂ) : Prop :=
  ∀ᵐ x ∂μ, F (autMk V x) = ψ x

structure IsReg (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))) : Prop where
  val : ∀ g F, ∀ᵐ x ∂μ, ρ g F (autMk V x) = F (autMk V (x * g))
  iso : ∀ g F, ‖ρ g F‖ = ‖F‖
  cont : ∀ F, Continuous fun g => ρ g F

def IsSmoothVector' (θ : InfFam D) (V : HSp D) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (F : K) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Mt V.rank), (∀ i, Xs i ∈ lieAt V (τs i)) →
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod F

def dL2 (θ : InfFam D) (V : HSp D) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (p : D.what₂.Tau × Mt V.rank) (F : K) : K :=
  deriv (fun t : ℝ => ρ (oneP θ V p.1 p.2 t) F) 0

structure GoodDict (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    {r : ℕ} (hr : V.rank = r) {Comp : Type} (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r)
    (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) (Kf : Subgroup (GA D V)) : Prop where
  inf : IsInfFam θ
  base : BaseFr M θ hr dict
  unif : ∃ th, (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr
  model : ∀ k, ModelW V hr (X k)
  muUnit : MuUnit V dict mu
  muCont : Continuous mu
  chi : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1
  cNe : ∀ k, c k ≠ 0
  cBdd : ∃ C : ℝ, ∀ k, ‖c k‖ ≤ C
  fin : Finite Comp
  levFin : Kf ≤ GfC V
  levOpen : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ Kf
  muK : ∀ k ∈ Kf, mu k = 1
  wt : ∃ e : D.what₂.Tau → ℤ, (∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ e ρ) ∧
    ∀ k ρ (τ : (X k).Ψ), τ.1 = tauE D ρ → ∀ a : Fin V.rank, w ρ a = la k τ (Fin.cast hr a) + e ρ

end Adelic

end GlobalTheory.HolDict
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsoRows
section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TowU

section Coord

variable {R : Type} [CommRing R] {κ κ₁ : Type}

variable [Fintype κ] [Fintype κ₁] {W W₁ : Type} [AddCommGroup W] [Module R W] [AddCommGroup W₁] [Module R W₁]
  {B : W → W → R} {B₁ : W₁ → W₁ → R}

end Coord

section Frame

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α α₁ ν : Type} [Fintype α] [DecidableEq α] [Fintype α₁] [DecidableEq α₁] [Fintype ν] [DecidableEq ν]

structure IsFrame (J : Matrix α α A) (C D : Matrix α ν A) (ι : Matrix α α₁ A) : Prop where
  cc : Cᵀ * J * C.map c = 0
  dd : Dᵀ * J * D.map c = 0
  cd : Cᵀ * J * D.map c = 1
  ic : ιᵀ * J * C.map c = 0
  ci : Cᵀ * J * ι.map c = 0
  id : ιᵀ * J * D.map c = 0
  di : Dᵀ * J * ι.map c = 0
  basis : ∃ M : Matrix ((ν ⊕ ν) ⊕ α₁) α A, Matrix.fromCols (Matrix.fromCols C D) ι * M = 1 ∧
    M * Matrix.fromCols (Matrix.fromCols C D) ι = 1

end Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


def IsRat {α β κ : Type} [Fintype κ] {B : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F} (d : Darboux B κ) : Prop :=
  ∀ x : Matrix α β E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

variable (σ : E →ₐ[F] E)

variable {σ}


end GlobalTheory.TowU

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
section
namespace GlobalTheory.ThK

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def KDecay : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → Decay B G om om'

def KConst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om' R Rf, IsMatched B G X om om' R Rf → OneConst B G X om om' R Rf

def KCoinv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om' R Rf, IsMatched B G X om om' R Rf → Coinv B G X om om' Rf

def KBeta : Prop :=
  ∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    StepBeta σ e₁ e₂ s

def KAlpha : Prop :=
  ∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    StepAlpha σ e₁ e₂ s

def KReal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∃ R, IsRealMaps B G om om' R

def KFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∃ Rf, IsFinMaps B G X om om' Rf

theorem agree_of_parts (h1 : KDecay) (h2 : KConst) (h3 : KCoinv) (h4 : KBeta) (h5 : KAlpha) : ThetaIntegralsAgree :=
  ⟨fun F E _ _ _ _ _ σ B a a' G X om om' h => ⟨h1 F E σ B a a' G X om om' h,
    fun R Rf m => ⟨h2 F E σ B a a' G X om om' R Rf m, h3 F E σ B a a' G X om om' R Rf m⟩⟩, h4, h5⟩

theorem matching_of_parts (h1 : KReal) (h2 : KFin) : LocalMatching := by
  unfold KReal at h1
  unfold KFin at h2
  intro F E _ _ _ _ _ σ B a a' G X om om' h
  obtain ⟨R, r⟩ := h1 F E σ B a a' G X om om' h
  obtain ⟨Rf, f⟩ := h2 F E σ B a a' G X om om' h
  exact ⟨R, Rf, h, r, f⟩

end GlobalTheory.ThK
end

