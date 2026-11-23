module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0004
public import ReciprocityTheory.SemistableReduction.Bundle0004
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTransposeMajorant
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower

namespace GlobalTheory.Proof.ConjugateTransposeMajorant

section

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem csum_eq_coord (S : CSD K) (f g : S.Forms) :
    S.csum (f : S.Cl → S.V) (g : S.Cl → S.V) = star (fun a => S.basis.repr f a) ⬝ᵥ S.H *ᵥ fun a => S.basis.repr g a := by
  have hf : ∀ c, (f : S.Cl → S.V) c = ∑ a, S.basis.repr f a • (S.basis a : S.Cl → S.V) c := by
    intro c
    conv_lhs => rw [← S.basis.sum_repr f]
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hg : ∀ c, (g : S.Cl → S.V) c = ∑ a, S.basis.repr g a • (S.basis a : S.Cl → S.V) c := by
    intro c
    conv_lhs => rw [← S.basis.sum_repr g]
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have e : ∀ c, S.pair ((f : S.Cl → S.V) c) ((g : S.Cl → S.V) c) =
      ∑ a, ∑ b, star (S.basis.repr f a) * (S.pair ((S.basis a : S.Cl → S.V) c) ((S.basis b : S.Cl → S.V) c) *
        S.basis.repr g b) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hf c, hg c, map_sum S.pair, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
    ring
  simp only [CSD.csum, CSD.H, e, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

omit [NumberField K] in
theorem map_conjTranspose_of_mem {m n : Type} (E : Matrix m n K) (hE : ∀ a k, E a k ∈ cmMax K) (σ : K →+* ℂ) :
    Eᴴ.map σ = (E.map σ)ᴴ := by
  ext i j
  exact hE j i σ

omit [NumberField K] [StarRing K] in
theorem map_mulVec' {m n : Type} [Fintype n] (E : Matrix m n K) (x : n → K) (σ : K →+* ℂ) :
    (fun a => σ ((E *ᵥ x) a)) = E.map σ *ᵥ fun k => σ (x k) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum]

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)

theorem repr_toF (x : Fin (B.dZ ℓ Z) → K) : (fun a => B.S.basis.repr (B.toF ℓ Z x) a) = B.fE ℓ Z *ᵥ x := by
  have : B.S.basis.equivFun (B.toF ℓ Z x) = B.fE ℓ Z *ᵥ x := by
    rw [BlockDat.fE, ← Matrix.mulVec_mulVec]
    exact B.S.basis.equivFun.apply_symm_apply _
  rw [← this]
  rfl

theorem HZ_eq : B.HZ ℓ Z = ((Nat.card ℓ.P : ℕ) : K)⁻¹ • ((B.fE ℓ Z)ᴴ * B.S.H * B.fE ℓ Z) := by
  have : B.HV ℓ = ((Nat.card ℓ.P : ℕ) : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl
  rw [BlockDat.HZ, this, BlockDat.fE, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem csumAt_toF (σ : K →+* ℂ) (x : Fin (B.dZ ℓ Z) → K) (u : B.S.Forms) :
    csumAt B.S σ (B.toF ℓ Z x) u = star (fun k => σ (x k)) ⬝ᵥ ((B.fE ℓ Z).map σ)ᴴ *ᵥ
      (B.S.H.map σ *ᵥ fun a => σ (B.S.basis.repr u a)) := by
  have h : (fun a => σ (B.S.basis.repr (B.toF ℓ Z x) a)) = (B.fE ℓ Z).map σ *ᵥ fun k => σ (x k) := by
    rw [← map_mulVec', ← repr_toF]
  unfold csumAt
  rw [h, Matrix.star_mulVec, Matrix.dotProduct_mulVec _ (((B.fE ℓ Z).map σ)ᴴ)]

end

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem majAt_eq_csumAt : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms), IsRatHerm (cmMax K) (B.HZ ℓ Z) (B.XQ ℓ Z) → (∀ a k, B.fE ℓ Z a k ∈ cmMax K) → (∀ (v : InfinitePlace K) x y, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y = ((Nat.card ℓ.P : ℕ) : ℂ)⁻¹ * csumAt B.S v.embedding (B.toF ℓ Z x) (B.toF ℓ Z y)) ∧ ∀ u : B.S.Forms, (∀ x, B.S.csum (B.toF ℓ Z x : B.S.Cl → B.S.V) (u : B.S.Cl → B.S.V) = 0) → ∀ (σ : K →+* ℂ) x, csumAt B.S σ (B.toF ℓ Z x) u = 0 := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z hH hE
  refine ⟨fun v x y => ?_, fun u hu σ x => ?_⟩
  · have h1 : ∀ w : Fin (B.dZ ℓ Z) → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K _) v w = fun k => v.embedding (w k) := by
      intro w; funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    have h2 : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y =
        star ((B.XQ ℓ Z v)⁻¹ *ᵥ fun k => v.embedding (x k)) ⬝ᵥ ((B.XQ ℓ Z v)⁻¹ *ᵥ fun k => v.embedding (y k)) := by
      simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h1]
      rfl
    have h3 : (fun a => v.embedding (B.S.basis.repr (B.toF ℓ Z y) a)) =
        (B.fE ℓ Z).map v.embedding *ᵥ fun k => v.embedding (y k) := by
      rw [← map_mulVec', ← repr_toF]
    have h4 : (B.HZ ℓ Z).map v.embedding = ((Nat.card ℓ.P : ℕ) : ℂ)⁻¹ •
        (((B.fE ℓ Z).map v.embedding)ᴴ * B.S.H.map v.embedding * (B.fE ℓ Z).map v.embedding) := by
      rw [← map_conjTranspose_of_mem _ hE, ← Matrix.map_mul, ← Matrix.map_mul, HZ_eq]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]
    rw [h2, csumAt_toF, h3, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, (hH.2 v).2, h4,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  · have h0 : (B.fE ℓ Z)ᴴ *ᵥ (B.S.H *ᵥ fun a => B.S.basis.repr u a) = 0 := by
      funext k
      have := hu (Pi.single k 1)
      rw [csum_eq_coord, repr_toF, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at this
      have e : star (Pi.single k (1 : K) : Fin (B.dZ ℓ Z) → K) = Pi.single k 1 := by
        rw [Pi.star_single, star_one]
      rw [e, single_dotProduct, one_mul] at this
      exact this
    rw [csumAt_toF, ← map_mulVec', ← map_conjTranspose_of_mem _ hE, ← map_mulVec', h0]
    simp

end GlobalTheory.Proof.ConjugateTransposeMajorant

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V leviV)
open GlobalTheory GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts

namespace GlobalTheory.SemiPosBir

variable {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Z ⟶ Sp k} {σ : k →+* ℂ}
  {D : ℕ}


open ReciprocityTheory.L2DbarEstimates in
theorem continuousAt_levi {g : V D → ℂ} {x : V D} (hg : ContDiffAt ℝ 2 g x) (ξ : Fin D → ℂ) :
    ContinuousAt (fun v => leviV D g v ξ) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
  have h2 : ∀ l, ContDiffAt ℝ 1 (wdb D l g) x := fun l =>
    ((h1.clm_apply contDiffAt_const).add
      (contDiffAt_const.mul (h1.clm_apply contDiffAt_const))).div_const 2
  have h3 : ∀ j l, ContinuousAt (wd D j (wdb D l g)) x := fun j l => by
    have h4 : ContinuousAt (fderiv ℝ (wdb D l g)) x :=
      ((h2 l).fderiv_right (m := 0) (by norm_num)).continuousAt
    exact ((h4.clm_apply continuousAt_const).sub
      (continuousAt_const.mul (h4.clm_apply continuousAt_const))).div_const 2
  unfold leviV
  exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun l _ =>
    ((h3 j l).mul continuousAt_const).mul continuousAt_const

theorem ae_mem [IsDomain k] [IsIntegral X] (hσ : Function.Injective σ) (c : AlgChart p σ D)
    {U : X.Opens} (hU : (U : Set X).Nonempty) :
    ∀ᵐ v : V D, v ∈ c.e.target → c.e.symm v ∈ ptsIn p σ U := by
  rcases c.e.source.eq_empty_or_nonempty with h | ⟨y, hy⟩
  · exact .of_forall fun v hv => absurd (c.e.map_target hv) (h ▸ notMem_empty _)
  have hy' := mem_ptsIn.1 (c.source_subset hy)
  obtain ⟨x, hx, hx'⟩ := nonempty_preirreducible_inter U.isOpen c.U.isOpen hU ⟨_, hy'⟩
  obtain ⟨a, ha, ha'⟩ := c.affine.exists_basicOpen_le (V := U) ⟨x, hx⟩ hx'
  have h0 : a ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at ha'
    exact ha'
  have : Nonempty c.U := ⟨⟨_, hy'⟩⟩
  let φ := MvPolynomial.eval₂Hom (algX p c.U) c.x
  let : Algebra (MvPolynomial (Fin D) k) Γ(X, c.U) := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin D) k) Γ(X, c.U) := c.etale
  have h₁ := isAlgebraic_of_flat_of_formallyUnramified (MvPolynomial (Fin D) k) Γ(X, c.U)
  obtain ⟨r, hr, b, hb⟩ := (h₁.isAlgebraic a).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero h0)
  have hr' : MvPolynomial.map σ r ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective σ hσ)).2 hr
  filter_upwards [ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear (volume : Measure (V D))
    (WithLp.linearEquiv 2 ℂ (Fin D → ℂ)) _ hr'] with v hv hvt
  have hs := c.e.map_target hvt
  have hz := c.source_subset hs
  refine ptsIn_mono ha ((mem_ptsIn_basicOpen hz a).2 fun e => hv ?_)
  have e₁ : (evHom hz).comp φ = (MvPolynomial.eval (WithLp.linearEquiv 2 ℂ (Fin D → ℂ) v)).comp
      (MvPolynomial.map σ) := by
    refine MvPolynomial.ringHom_ext (fun t => ?_) fun i => ?_
    · simp only [φ, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C,
        MvPolynomial.eval_C, ← ev_eq, ev_algX hz]
    · simp only [φ, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
        MvPolynomial.eval_X, ← ev_eq, ← c.apply_eq _ hs, c.e.right_inv hvt]
      rfl
  have e₂ : φ r = a * b := hb
  refine (RingHom.congr_fun e₁ r).symm.trans ?_
  rw [RingHom.comp_apply, e₂, ← ev_eq, ev_mul, e, zero_mul]


variable (D) in
def PosOn (f : CxPts p σ → ℝ) (S : Set (CxPts p σ)) : Prop :=
  ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source ∩ S, ∀ ξ : Fin D → ℂ,
    0 ≤ (leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e y) ξ).re

theorem PosOn.of_inter [IsDomain k] [IsIntegral X] (hσ : Function.Injective σ)
    {f : CxPts p σ → ℝ} {S : Set (CxPts p σ)} (hS : IsOpen S) (hf : ∀ y ∈ S, CInfAt f y)
    {U : X.Opens} (hU : (U : Set X).Nonempty) (h : PosOn D f (S ∩ ptsIn p σ U)) :
    PosOn D f S := fun c y hy ξ => by
  have ho := (isOpen_over c.e hS).mem_nhds (mem_over c.e hy.1 hy.2)
  have hd : ContDiffAt ℝ 2 (fun v => f (c.e.symm v)) (c.e y) :=
    ((contDiffOn_chart hf c).contDiffAt ho).of_le (by norm_cast)
  have hc := Complex.continuous_re.continuousAt.comp
    (continuousAt_levi (Complex.ofRealCLM.contDiff.contDiffAt.comp _ hd) ξ)
  have hfr := (mem_closure_iff_frequently.1 ((Measure.dense_of_ae (ae_mem hσ c hU)) (c.e y)))
  refine isClosed_Ici.mem_of_frequently_of_tendsto ((hfr.and_eventually ho).mono ?_) hc
  rintro v ⟨h₁, h₂, h₃⟩
  have := h c _ ⟨c.e.map_target h₂, h₃, h₁ h₂⟩ ξ
  rwa [c.e.right_inv h₂] at this

theorem levi_pull {j : Z ⟶ X} (hj : j ≫ p = q) (f : CxPts p σ → ℝ) (c : AlgChart p σ D)
    (c' : AlgChart q σ D) (e : c'.U ≤ j ⁻¹ᵁ c.U) (hx : ∀ a, c'.x a = (j.appLE _ _ e).hom (c.x a))
    {z : CxPts q σ} (hz : z ∈ c'.e.source) (hz' : PtsOver.map j hj _ z ∈ c.e.source)
    (ξ : Fin D → ℂ) :
    leviV D (fun v => (f (PtsOver.map j hj _ (c'.e.symm v)) : ℂ)) (c'.e z) ξ =
      leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e (PtsOver.map j hj _ z)) ξ := by
  have he (w) (hw : w ∈ c'.e.source) (hw' : PtsOver.map j hj (spMap σ) w ∈ c.e.source) :
      c'.e w = c.e (PtsOver.map j hj (spMap σ) w) := by
    ext a
    rw [c'.apply_eq w hw, c.apply_eq _ hw', hx]
    exact valR_appLE w.1 j e (c'.source_subset hw) _
  have hS : IsOpen (c'.e.source ∩ PtsOver.map j hj (spMap σ) ⁻¹' c.e.source) :=
    c'.e.open_source.inter (c.e.open_source.preimage (PtsOver.continuous_map j hj _))
  rw [← he z hz hz']
  refine ReciprocityTheory.L2DbarEstimates.leviV_congr ?_ ξ
  filter_upwards [(isOpen_over c'.e hS).mem_nhds (mem_over c'.e hz (S := _) ⟨hz, hz'⟩)] with v hv
  have e₁ : c.e.symm v = PtsOver.map j hj _ (c'.e.symm v) := by
    have := he _ hv.2.1 hv.2.2
    rw [c'.e.right_inv hv.1] at this
    exact (congrArg c.e.symm this).trans (c.e.left_inv hv.2.2)
  rw [e₁]

theorem appLE_comp_eval {j : Z ⟶ X} (hj : j ≫ p = q) {U : X.Opens} {W : Z.Opens}
    (e : W ≤ j ⁻¹ᵁ U) (x : Fin D → Γ(X, U)) :
    (j.appLE U W e).hom.comp (MvPolynomial.eval₂Hom (algX p U) x) =
      MvPolynomial.eval₂Hom (algX q W) fun a => (j.appLE U W e).hom (x a) := by
  subst hj
  refine MvPolynomial.ringHom_ext (fun t => ?_) fun i => ?_
  · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    exact congrArg (fun g : Γ(Sp k, ⊤) ⟶ Γ(Z, W) => g.hom ((Scheme.ΓSpecIso (.of k)).inv.hom t))
      (Scheme.Hom.appLE_comp_appLE j p ⊤ U W le_top e)
  · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

theorem exists_map_eq (j : Z ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ j.opensRange) : ∃ z : CxPts q σ, PtsOver.map j hj _ z = y := by
  have H : Set.range y.1 ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    exact hy (x := x) trivial
  refine ⟨⟨IsOpenImmersion.lift j y.1 H, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac]
  exact y.2

theorem PosOn.pull (j : Z ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)} (h : PosOn D f S) :
    PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S) :=
  fun c' z hz ξ => by
  have e : c'.U ≤ j ⁻¹ᵁ j ''ᵁ c'.U := (j.preimage_image_eq _).ge
  have hi : IsIso (j.appLE _ _ e) := by
    rw [← Scheme.Hom.appIso_hom']
    infer_instance
  have hb := ConcreteCategory.bijective_of_isIso (j.appLE _ _ e)
  choose x hx using fun a => hb.2 (c'.x a)
  have h₁ := appLE_comp_eval hj e x
  have h₂ : (MvPolynomial.eval₂Hom (algX p (j ''ᵁ c'.U)) x).Etale := by
    refine (RingHom.Etale.respectsIso.cancel_right_isIso (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom (algX p (j ''ᵁ c'.U)) x)) (j.appLE _ _ e)).1 ?_
    change ((j.appLE _ _ e).hom.comp (MvPolynomial.eval₂Hom (algX p (j ''ᵁ c'.U)) x)).Etale
    rw [h₁, show (fun a => (j.appLE _ _ e).hom (x a)) = c'.x from funext hx]
    exact c'.etale
  obtain ⟨c, hc, hU, hcx⟩ := AlgChart.exists_of_etale (y := PtsOver.map j hj (spMap σ) z)
    (c'.affine.image_of_isOpenImmersion j) x h₂
    (mem_ptsIn.2 ⟨_, mem_ptsIn.1 (c'.source_subset hz.1), rfl⟩)
  have key : ∀ (U : X.Opens) (hU : c.U = U) (e : c'.U ≤ j ⁻¹ᵁ U) (x : Fin D → Γ(X, U)),
      c.x = hU ▸ x → (∀ a, (j.appLE _ _ e).hom (x a) = c'.x a) →
      ∃ e : c'.U ≤ j ⁻¹ᵁ c.U, ∀ a, c'.x a = (j.appLE _ _ e).hom (c.x a) := by
    rintro _ rfl e x h₁ h₂
    exact ⟨e, fun a => by rw [h₁]; exact (h₂ a).symm⟩
  obtain ⟨e', hx'⟩ := key _ hU e x hcx hx
  rw [levi_pull hj f c c' e' hx' hz.1 hc]
  exact h c _ ⟨hc, hz.2⟩ ξ

theorem PosOn.of_pull (j : Z ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)}
    (h : PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S)) :
    PosOn D f (S ∩ ptsIn p σ j.opensRange) := fun c y hy ξ => by
  obtain ⟨z, rfl⟩ := exists_map_eq j hj hy.2.2
  obtain ⟨W, hW, hzW, e⟩ := exists_isAffineOpen_le z.1 (V := j ⁻¹ᵁ c.U) (c.source_subset hy.1)
  have h₂ : (MvPolynomial.eval₂Hom (algX q W) fun a => (j.appLE _ W e).hom (c.x a)).Etale := by
    rw [← appLE_comp_eval hj e]
    exact RingHom.Etale.stableUnderComposition _ _ c.etale
      (HasRingHomProperty.appLE @Etale j inferInstance ⟨c.U, c.affine⟩ ⟨W, hW⟩ e)
  obtain ⟨c', hc, rfl, hcx⟩ := AlgChart.exists_of_etale (y := z) hW _ h₂ hzW
  rw [← levi_pull hj f c c' e (congrFun hcx) hc hy.1]
  exact h c' _ ⟨hc, hy.2.1⟩ ξ

theorem posOn_iff_pull [IsDomain k] [IsIntegral X] (hσ : Function.Injective σ) (j : Z ⟶ X)
    [IsOpenImmersion j] [Nonempty Z] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)} (hS : IsOpen S) (hf : ∀ y ∈ S, CInfAt f y) : PosOn D f S ↔
    PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S) :=
  ⟨fun h => h.pull j hj, fun h => (h.of_pull j hj).of_inter hσ hS hf (range_nonempty _)⟩

theorem semiPos_iff_pull : ∀ (k : Type) [CommRing k] (X X' : Scheme.{0}) (p : X ⟶ Sp k) (q : X' ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : X' ⟶ X) (hπ : π ≫ p = q) (U : X.Opens), (U : Set X).Nonempty → IsIso (π ∣_ U) → ∀ L : HermLB p, (L.SemiPos D ↔ (L.pull π hπ).SemiPos D) := by
  intro k _ X X' p q D hp hq π hπ U hU hi L
  have := hp.isDomain
  have := hp.finite
  have := hp.isIntegral
  have := hq.isIntegral
  refine forall_congr' fun σ => ?_
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have : Nonempty U.toScheme := hU.to_subtype
  have : Nonempty (π ⁻¹ᵁ U).toScheme := (π ∣_ U).surjective.nonempty
  have : IsOpenImmersion ((π ⁻¹ᵁ U).ι ≫ π) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have key (i : L.B.ι) : PosOn D ((L.φ σ).φ i) (ptsIn p σ (L.B.U i)) ↔
      PosOn D (fun w => (L.φ σ).φ i (PtsOver.map π hπ _ w))
        (PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ (L.B.U i)) := by
    rw [posOn_iff_pull hσ ((π ⁻¹ᵁ U).ι ≫ π) rfl (isOpen_ptsIn _) (L.cInf σ i),
      posOn_iff_pull hσ (π ⁻¹ᵁ U).ι (q := ((π ⁻¹ᵁ U).ι ≫ π) ≫ p) (by rw [Category.assoc, hπ])
        ((isOpen_ptsIn _).preimage (PtsOver.continuous_map π hπ _))
        fun y hy => CInfAt.pull π hπ (L.cInf σ i _ hy)]
    have e (w : CxPts (((π ⁻¹ᵁ U).ι ≫ π) ≫ p) σ) : PtsOver.map ((π ⁻¹ᵁ U).ι ≫ π) rfl _ w =
        PtsOver.map π hπ _ (PtsOver.map (π ⁻¹ᵁ U).ι (by rw [Category.assoc, hπ]) _ w) :=
      Subtype.ext (Category.assoc _ _ _).symm
    rw [funext e]
    simp only [e]
    rfl
  have e₁ (J : (L.B.pull π).ι) : ptsIn q σ ((L.B.pull π).U J) =
      PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ (L.B.U (J PUnit.unit)) := Set.ext fun z => by
    rw [mem_preimage, mem_ptsIn, mem_ptsIn]
    exact ⟨fun h => mem_iInter.1 h PUnit.unit, fun h => mem_iInter.2 fun _ => h⟩
  have e₂ (J : (L.B.pull π).ι) : ((L.φ σ).pull π hπ).φ J =
      fun w => (L.φ σ).φ (J PUnit.unit) (PtsOver.map π hπ _ w) :=
    funext ((L.φ σ).pull_φ π hπ J)
  change (∀ i, PosOn D ((L.φ σ).φ i) (ptsIn p σ (L.B.U i))) ↔
    ∀ J, PosOn D (((L.φ σ).pull π hπ).φ J) (ptsIn q σ ((L.B.pull π).U J))
  simp only [e₁, e₂, key]
  exact ⟨fun h J => h _, fun h i => h fun _ => i⟩

end GlobalTheory.SemiPosBir
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordEqOfPerConj
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

section Letters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_of_mem (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) :
    perFr X x v τ.1 i =
      if hi : X.p0 + i < r then ((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) ⟨X.p0 + i, hi⟩ else 0 := by
  unfold perFr
  rw [dite_eq_left τ.2]

theorem perFr_of_conj (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) (j : Fin r)
    (hj : (j : ℕ) = X.p0 - 1 - i) :
    perFr X x v (conjEmb τ.1) i = hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
  have hcc : conjEmb (conjEmb τ.1) = τ.1 := by
    ext a; simp [conjEmb]
  have h1 : conjEmb τ.1 ∉ X.Ψ := (X.cmType τ.1).1 τ.2
  have h2 : conjEmb (conjEmb τ.1) ∈ X.Ψ := by rw [hcc]; exact τ.2
  have h3 : X.p0 - 1 - i < r := hj ▸ j.2
  unfold perFr
  rw [dite_eq_right h1, dite_eq_left h2, dite_eq_left h3]
  have key : ∀ (σ : E →+* ℂ) (hσ : σ ∈ X.Ψ), σ = τ.1 →
      hermC σ X.Gm (FD.col (mat x ⟨σ, hσ⟩) ⟨X.p0 - 1 - i, h3⟩) (Data.emb σ v) =
        hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
    intro σ hσ h
    subst h
    have : (⟨X.p0 - 1 - i, h3⟩ : Fin r) = j := Fin.ext hj.symm
    rw [this]
  exact key _ h2 hcc

theorem coord_eq_of_per_mem (X : Data E r) (τ : X.Ψ) (a : Fin r) (ha : X.p0 ≤ (a : ℕ)) (i : ℕ)
    (h : ∀ x v, per X x v (τ, a) = perFr X x v τ.1 i) : (a : ℕ) = X.p0 + i := by
  obtain ⟨x, hm⟩ : ∃ x : Frame X.Ψ r, mat x τ = 1 := ⟨fun _ => (1 : Matrix (Fin r) (Fin r) ℂ), rfl⟩
  have h1 := h x (Pi.single a 1)
  rw [per_of_le X _ _ _ ha, perFr_of_mem, hm, inv_one, one_mulVec] at h1
  by_contra hne
  split_ifs at h1 with hi
  · have h2 : (⟨X.p0 + i, hi⟩ : Fin r) ≠ a := fun e => hne (by rw [← e])
    simp [Data.emb, Pi.single_eq_of_ne h2] at h1
  · simp [Data.emb] at h1

theorem coord_eq_of_per_conj (X : Data E r) (τ : X.Ψ) (a : Fin r) (ha : (a : ℕ) < X.p0) (i : ℕ)
    (h : ∀ x v, per X x v (τ, a) = perFr X x v (conjEmb τ.1) i) : (a : ℕ) = X.p0 - 1 - i := by
  have hle := X.p0_le
  obtain ⟨s, t, hst⟩ : ∃ s t, X.Gm s t ≠ 0 := by
    by_contra hc
    push Not at hc
    exact X.Gm_det (Matrix.det_eq_zero_of_row_eq_zero a (hc a))
  obtain ⟨x, hm⟩ : ∃ x : Frame X.Ψ r, mat x τ = Matrix.single s a 1 :=
    ⟨fun _ => (Matrix.single s a 1 : Matrix (Fin r) (Fin r) ℂ), rfl⟩
  have h1 := h x (Pi.single t 1)
  rw [per_of_lt X _ _ _ ha, perFr_of_conj X _ _ τ i ⟨X.p0 - 1 - i, by omega⟩ rfl, hm] at h1
  by_contra hne
  have h2 : a ≠ (⟨X.p0 - 1 - i, by omega⟩ : Fin r) := fun e => hne (by rw [e])
  simp [hermC, FD.col, Data.emb, Matrix.single_apply, Pi.single_apply, h2, apply_ite, hst] at h1

theorem Dic.letter {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} {σ : c.F →+* ℂ}
    {X : Data E r} {g q0 n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} (Dc : Dic Dw c σ X g q0 n a)
    (hσ : ∀ τ, Formalism.L2.PjFree.relab c σ τ = τ) (hm : ∀ τ, τ ∉ X.Ψ → Dw.mult τ ≤ X.p0) (ℓ : LtN Dw n) :
    (Dc.eL ℓ).2.2 = ℓ.2.2 ∧
      ((∃ k, (Dc.eL ℓ).2.1 = Sum.inl k ∧ ℓ.1 = (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1) ∨
       (∃ k, (Dc.eL ℓ).2.1 = Sum.inr k ∧ ℓ.1 = conjEmb (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1)) := by
  have hd := Dc.dir_eq ℓ
  generalize Dc.eL ℓ = L at hd ⊢
  obtain ⟨t, ρ, b⟩ := L
  obtain ⟨τ, i, b'⟩ := ℓ
  simp only [letterDir] at hd ⊢
  have hb : b = b' := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    simp [Pi.single_eq_of_ne hne] at this
  subst hb
  have hj : Dc.idx.symm (rowOf X Dc.hr (t, ρ)) = Dc.e.symm ⟨τ, i⟩ := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    exact one_ne_zero this
  have hi : Dc.idx (Dc.e.symm ⟨τ, i⟩) = (t, rowIdx Dc.hr ρ) := by rw [← hj, Equiv.apply_symm_apply]; rfl
  have hty := Dc.ty_eq (Dc.e.symm ⟨τ, i⟩)
  have hper : ∀ x v, per X x v (t, rowIdx Dc.hr ρ) = perFr X x v τ i := fun x v => by
    have := Dc.per_eq x v (Dc.e.symm ⟨τ, i⟩)
    rwa [pv, Function.comp_apply, hi, hσ, Equiv.apply_symm_apply] at this
  rw [hi, hσ, Equiv.apply_symm_apply] at hty
  refine ⟨rfl, ?_⟩
  rcases ρ with k | k
  · have h1 : τ = t.1 := hty.symm.trans (rowType_rowOf_inl X Dc.hr t k)
    subst h1
    have h2 := coord_eq_of_per_mem X t _ (by simp) i hper
    rw [rowIdx_inl] at h2
    exact Or.inl ⟨k, rfl, rfl, by omega⟩
  · have h1 : τ = conjEmb t.1 := hty.symm.trans (rowType_rowOf_inr X Dc.hr t k)
    subst h1
    have hk := k.2
    have h2 := coord_eq_of_per_conj X t _ (by rw [rowIdx_inr]; omega) i hper
    rw [rowIdx_inr] at h2
    have h3 := hm _ ((X.cmType t.1).1 t.2)
    have h4 : (i : ℕ) < X.p0 := lt_of_lt_of_le i.2 h3
    exact Or.inr ⟨k, rfl, rfl, by omega⟩

end Letters


end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointsFiniteEtaleFreeEqRankStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_complexPoints_finiteEtaleFree_eq_rank : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (δ : ℕ), f.Etale → f.Finite → (letI := f.toAlgebra; Module.Free A B ∧ Module.finrank A B = δ) → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (δ : ℕ∞) := by
  first | exact @GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank | exact GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank | (intros; apply GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank <;> assumption)
end

