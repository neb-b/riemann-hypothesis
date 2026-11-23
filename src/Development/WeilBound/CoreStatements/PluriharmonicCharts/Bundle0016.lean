module

public import Mathlib
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.MapSumMinor
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsBlockMapInitialVertex
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqDiag
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0031

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsPenFrame
section
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

namespace PositivityTheory.Xgp.W

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

theorem exists_penFrame {τ : Ψ} {a b ca cb : Fin N} {k₀ : K} (hb : (b : ℕ) = a + 1)
    (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hk : M.blk (τ, a) = some k₀) (hca : (ca : ℕ) = lastCol N j a)
    (hcb : (cb : ℕ) = ca + 1) {z : (Σ k, ι k) → L} (hz : IsPt y z) (c : ∀ k, ι k) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) :
    Nonempty (PenFrame y k₀ (vecB M τ a k₀ ca cb) (cFac M τ a) (eDeg M τ a k₀) z c) := by
  obtain ⟨cb', hcb'⟩ := Classical.axiomOfChoice (isPt_base M hz).1
  obtain ⟨F, hF, hG⟩ := M.frames _ (RingHom.ker_isPrime _) (CoordinateConeArithVar.relevant _ cb' hcb')
    (isPt_base M hz).le
  have hG' : M.GoodAt F (mCoordIdeal (basePart M.blk z)) := hG
  choose uv huv using fun q I => exists_hasVal_of_regAt (hG'.2.1 q I).1
  have hυ : ∀ i, ∃ v, M.blk (τ, i) = none → HasVal M.x (basePart M.blk z) (F.υ (τ, i)) v := fun i => by
    by_cases h : M.blk (τ, i) = none
    · exact (exists_hasVal_of_regAt (hG'.2.2 _ h).2.1).imp fun _ hv _ => hv
    · exact ⟨0, fun h' => absurd h' h⟩
  choose υv hυ using hυ
  obtain ⟨PF, -⟩ := core M ⟨M.j_le, hb, hab, hca, hcb⟩ hk hz c hc hF hG' uv huv υv hυ
  exact ⟨PF⟩

end PositivityTheory.Xgp.W
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsPositivePeriodLine
section
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

open GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem exists_lift_gen {A F E : Type} [CommRing A] [Field F] [Field E] (a : A →+* F) (b : A →+* E)
    (hk : RingHom.ker a = RingHom.ker b) (gen : ∀ c, ∃ f g, c = a f / a g) : ∃ ψ : F →+* E, ∀ f, ψ (a f) = b f := by
  letI : Algebra (A ⧸ RingHom.ker a) F := (RingHom.kerLift a).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker a) F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective a)
  haveI : IsFractionRing (A ⧸ RingHom.ker a) F := IsFractionRing.of_field _ _ fun c => by
    obtain ⟨f, g, e⟩ := gen c
    exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, e⟩
  let b' : A ⧸ RingHom.ker a →+* E := Ideal.Quotient.lift _ b fun f hf => by rwa [hk] at hf
  have hb' : Function.Injective b' := RingHom.lift_injective_of_ker_le_ideal _ _ hk.ge
  exact ⟨IsFractionRing.lift hb', fun f => IsFractionRing.lift_algebraMap hb' (Ideal.Quotient.mk _ f)⟩

def fibEquiv (ι : K → Type) (k₀ : K) :
    (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) ≃ ι k₀ where
  toFun
    | ⟨⟨some k, h⟩, _⟩ => absurd ⟨k, rfl⟩ h
    | ⟨⟨none, _⟩, m⟩ => m
  invFun m := ⟨⟨none, by rintro ⟨k, hk⟩; cases hk⟩, m⟩
  left_inv := by
    rintro ⟨⟨_ | k, h⟩, m⟩
    · rfl
    · exact absurd ⟨k, rfl⟩ h
  right_inv _ := rfl

theorem fibreBlock_subsingleton (k k' : FibreBlock (some : K → Option K)) : k = k' := by
  rcases k with ⟨_ | k, hk⟩
  · rcases k' with ⟨_ | k', hk'⟩
    · rfl
    · exact absurd ⟨k', rfl⟩ hk'
  · exact absurd ⟨k, rfl⟩ hk

theorem isMultiHomog_lin {F : Type} [Field F] (k₀ : K)
    (μ : (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) → F) :
    IsMultiHomog (∑ q, C (μ q) * X q : MRingOver F (fibreIdx (iW ι k₀) some)) fun _ => 1 := by
  intro s hs k
  obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (support_sum hs)
  rw [C_mul_X_eq_monomial] at hq
  have hs' := support_monomial_subset hq
  rw [Finset.mem_singleton] at hs'
  subst hs'
  obtain ⟨qk, qi⟩ := q
  obtain rfl : qk = k := fibreBlock_subsingleton _ _
  simp [Finsupp.single_apply]

variable {y : (Σ k, ι k) → Φ} {k₀ : K} {B : ι k₀ → Φ}

theorem cone_homog {E : Type} [Field E] (i₀ : MvPolynomial K Φ →+* E) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) : i₀ (mConeMap y g) = (∏ k, i₀ (X k) ^ d k) * i₀ (C (aeval y g)) := by
  have e : i₀.comp (mConeMap y).toRingHom =
      (aeval (fun p : Σ k, ι k => i₀ (X p.1) * ((i₀.comp C) ∘ y) p) : MRing ι →ₐ[ℤ] E).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) fun p => by simp [mConeMap, mul_comm]
  have := RingHom.congr_fun e g
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this, aeval_scale' (fun k => i₀ (X k)) _ hg, CPts.aeval_comp_ringHom]
  rfl

theorem exists_positive_period_line {E : Type} [Field E] (i₀ : MvPolynomial K Φ →+* E) (hi : Function.Injective i₀)
    {cf : Φ} {e : K → ℤ} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e y c)
    (G : GenFibre (v₀ k₀) (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X))) :
    ∃ T : Set (MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K))),
      (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T := by
  let a : MRing ι →+* G.Φ := (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom
  have hka : RingHom.ker a = mCoordIdeal y := G.ker_x.trans (image_pen _ _ _ _ _)
  obtain ⟨ψ, hψ⟩ := exists_lift_gen a (i₀.comp (mConeMap y).toRingHom)
    (by rw [hka, RingHom.ker_comp_of_injective _ hi]; rfl)
    (fun c => by obtain ⟨f, g, -, e⟩ := G.gen c; exact ⟨f, g, e⟩)
  have lift : ∀ s v, HasVal y y s v → ∃ s', ψ s' = i₀ (C s) := by
    rintro s v ⟨d, g, h, hg, hh, h0, e, -⟩
    refine ⟨a g / a h, ?_⟩
    rw [map_div₀, hψ, hψ]
    show i₀ (mConeMap y g) / i₀ (mConeMap y h) = _
    have hp : (∏ k, i₀ (X k) ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ ((map_ne_zero_iff _ hi).2 (X_ne_zero _))
    have h1 : i₀ (C (aeval y h)) ≠ 0 := (map_ne_zero_iff _ hi).2 (by rwa [Ne, C_eq_zero])
    rw [cone_homog i₀ hg, cone_homog i₀ hh, mul_div_mul_left _ _ hp, e, map_mul, map_mul,
      mul_div_cancel_right₀ _ h1]
  choose p hp using fun m => lift _ _ (Fr.hp m)
  choose r hr using fun m => lift _ _ (Fr.hr m)
  choose α hα using fun m => lift _ _ (Fr.hα m)
  choose β hβ using fun m => lift _ _ (Fr.hβ m)
  let eF := fibEquiv ι k₀
  let ℓ : (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) → Fin 2 → G.Φ :=
    fun q => ![p (eF q), r (eF q)]
  have hν : ∀ a b : Fin 2, ∑ q, ![fun q => α (eF q), fun q => β (eF q)] a q * ℓ q b = if a = b then 1 else 0 := by
    have key : ∀ (u w : ι k₀ → G.Φ) (u' w' : ι k₀ → Φ) (s : G.Φ) (s' : Φ), (∀ m, ψ (u m) = i₀ (C (u' m))) →
        (∀ m, ψ (w m) = i₀ (C (w' m))) → ψ s = i₀ (C s') → ∑ m, u' m * w' m = s' →
        ∑ q, u (eF q) * w (eF q) = s := fun u w u' w' s s' hu hw hs h => by
      rw [Equiv.sum_comp eF fun m => u m * w m]
      apply ψ.injective
      rw [hs, ← h]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hu, hw]
    intro a b
    fin_cases a <;> fin_cases b
    · exact key α p _ _ 1 1 hα hp (by simp) Fr.αp
    · exact key α r _ _ 0 0 hα hr (by simp) Fr.αr
    · exact key β p _ _ 0 0 hβ hp (by simp) Fr.βp
    · exact key β r _ _ 1 1 hβ hr (by simp) Fr.βr
  refine ⟨linKerForms ℓ, ?_, ?_⟩
  · rintro f ⟨μ, -, rfl⟩
    exact isMultiHomog_lin k₀ μ
  rw [← ker_linSubst ℓ _ hν]
  let W' : MRing (iW ι k₀) →+* MvPolynomial (Fin 2) E := (MvPolynomial.map i₀).comp (planeMap y k₀ Fr.p Fr.r)
  let x' : MRing (iW ι k₀) →+* G.Φ' := (aeval G.x' : MRing (iW ι k₀) →ₐ[ℤ] G.Φ').toRingHom
  have hker : RingHom.ker x' = RingHom.ker W' := by
    rw [RingHom.ker_comp_of_injective _ (MvPolynomial.map_injective _ hi), ← Fr.ker_eq, ← ideal_pen_plane]
    exact G.genericFibre_ker_target
  have r1 : ∀ f, x' (rename (v₀ k₀) f) = algebraMap G.Φ G.Φ' (a f) := fun f => by
    have e : x'.comp (rename (v₀ k₀) : MRing ι →ₐ[ℤ] MRing (iW ι k₀)).toRingHom = (algebraMap G.Φ G.Φ').comp a :=
      MvPolynomial.ringHom_ext (fun r => by simp) fun q => by simpa [x', a] using G.compat q
    exact RingHom.congr_fun e f
  have r2 : ∀ f, W' (rename (v₀ k₀) f) = C (ψ (a f)) := fun f => by
    rw [hψ]
    have e : W'.comp (rename (v₀ k₀) : MRing ι →ₐ[ℤ] MRing (iW ι k₀)).toRingHom =
        (C : E →+* _).comp (i₀.comp (mConeMap y).toRingHom) :=
      MvPolynomial.ringHom_ext (fun r => by simp) fun q => by simp [W', planeMap, ext2, v₀, mConeMap]
    exact RingHom.congr_fun e f
  have main : ∀ f : MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K)), ∃ (Dn : MRing ι) (f' : MRing (iW ι k₀)),
      a Dn ≠ 0 ∧ x' f' = algebraMap G.Φ G.Φ' (a Dn) *
        aeval (fun q : Σ k : FibreBlock (some : K → Option K), iW ι k₀ k.1 => G.x' ⟨q.1.1, q.2⟩) f ∧
      W' f' = C (ψ (a Dn)) * MvPolynomial.map ψ (linSubst ℓ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C s =>
      obtain ⟨f, g, hg, e⟩ := G.gen s
      have e' : a f = a g * s := by rw [e]; exact (mul_div_cancel₀ _ hg).symm
      refine ⟨g, rename (v₀ k₀) f, hg, ?_, ?_⟩
      · rw [r1, e', map_mul, aeval_C]
      · rw [r2, e', map_mul, map_mul, algHom_C, algebraMap_eq, map_C]
    | add f g hf hg =>
      obtain ⟨D₁, f₁, h₁, a₁, b₁⟩ := hf
      obtain ⟨D₂, f₂, h₂, a₂, b₂⟩ := hg
      refine ⟨D₁ * D₂, f₁ * rename (v₀ k₀) D₂ + f₂ * rename (v₀ k₀) D₁, by rw [map_mul]; exact mul_ne_zero h₁ h₂,
        ?_, ?_⟩
      · simp only [map_add (f := _), map_mul, r1, a₁, a₂]; ring
      · simp only [map_add (f := _), map_mul, r2, b₁, b₂]; ring
    | mul_X f q hf =>
      obtain ⟨D₁, f₁, h₁, a₁, b₁⟩ := hf
      refine ⟨D₁, f₁ * X ⟨q.1.1, q.2⟩, h₁, ?_, ?_⟩
      · rw [map_mul, map_mul, a₁, aeval_X, mul_assoc]
        congr 2
        exact aeval_X _ _
      · rw [map_mul, map_mul, map_mul, b₁, mul_assoc]
        congr 2
        obtain ⟨m, rfl⟩ := eF.symm.surjective q
        have : W' (X ⟨none, m⟩) = C (i₀ (C (Fr.p m))) * X 0 + C (i₀ (C (Fr.r m))) * X 1 := by
          simp [W', planeMap, ext2]
        refine this.trans ?_
        simp [linSubst, ℓ, Fin.sum_univ_two, hp, hr]
  ext f
  obtain ⟨Dn, f', h0, h1, h2⟩ := main f
  have h3 : x' f' = 0 ↔ W' f' = 0 := SetLike.ext_iff.1 hker f'
  rw [h1, h2, mul_eq_zero, mul_eq_zero, or_iff_right ((map_ne_zero _).2 h0),
    or_iff_right (by rw [C_eq_zero]; exact (map_ne_zero _).2 h0),
    map_eq_zero_iff _ (MvPolynomial.map_injective _ ψ.injective)] at h3
  exact h3

theorem line_pen {cf : Φ} {e : K → ℤ} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e y c)
    (G : GenFibre (v₀ k₀) (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X))) :
    ∃ T : Set (MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K))),
      (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T :=
  exists_positive_period_line (algebraMap _ (FractionRing (MvPolynomial K Φ))) (IsFractionRing.injective _ _) Fr G

end PositivityTheory.Xgp.W
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqR
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.sq_R

open GroundTheory.Heights₂.Heights.Inter GroundTheory.Heights₂.Heights.Inter.DiagRAux

theorem smooth_pull {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)} (hb : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (hp : IsPullHerm κ v A A') : IsSmoothHerm A' := by
  have hfun : A'.h = fun z => A.h (fun p => z (v p)) := funext hp.2
  unfold IsSmoothHerm
  rw [hfun]
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Σ k, ι' k) → ℂ => fun p => z (v p)) :=
    contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (v p)
  refine hA.comp hlin.contDiffOn ?_
  intro z hz k
  obtain ⟨i, hi⟩ := hz (κ k)
  obtain ⟨⟨k1, i1⟩, hp1⟩ := hb.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
  have h1 : κ k1 = κ k := by
    have := hb.2.2.1 ⟨k1, i1⟩
    rw [hp1] at this
    exact this.symm
  obtain rfl := hb.1 h1
  exact ⟨i1, by show z (v ⟨k1, i1⟩) ≠ 0; rw [hp1]; exact hi⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cons_eq_snoc {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι} {A : HermLine ι} (hP : IsArithVar P (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) :
    I P (n + 1) (Fin.cons A L) = I P (n + 1) (Fin.snoc L A) := by
  have hrot := hI.1 P (n + 1) (Fin.cons A L) (finRotate (n + 1)) hP (smooth_cons hA hL)
  have hsnoc : (Fin.cons A L : Fin (n + 1) → HermLine ι) ∘ finRotate (n + 1) = Fin.snoc L A :=
    (Fin.snoc_eq_cons_rotate L A).symm
  rw [hsnoc] at hrot
  exact hrot.symm

theorem sq_sub {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hF : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι} {X₀ X₁ : HermLine ι} (hW : IsArithVar P (n + 2))
    (hL : ∀ j, IsSmoothHerm (L j)) (hs0 : IsSmoothHerm X₀) (hs1 : IsSmoothHerm X₁) (c : K → ℤ)
    (hdeg : ∀ k, 2 * c k = -(X₀.a k + X₁.a k)) :
    I P (n + 2) (Fin.cons X₀ (Fin.cons X₀ L)) - I P (n + 2) (Fin.cons X₁ (Fin.cons X₁ L)) =
      -2 * (I P (n + 2) (Fin.snoc (Fin.cons X₀ L : Fin (n + 1) → HermLine ι) (halfInvLine X₀ X₁ c hdeg)) -
        I P (n + 2) (Fin.snoc (Fin.cons X₁ L : Fin (n + 1) → HermLine ι) (halfInvLine X₀ X₁ c hdeg))) := by
  set Q := X₀.tensor X₁ with hQ
  set LL := halfInvLine X₀ X₁ c hdeg with hLL
  have hsQ : IsSmoothHerm Q := DiagRAux.isSmoothHerm_tensor hs0 hs1
  have hsLL : IsSmoothHerm LL := isSmoothHerm_halfInvLine hs0 hs1 _ hdeg
  set T2 := Q.tensor (LL.tensor LL) with hT2
  have hsT2 : IsSmoothHerm T2 := DiagRAux.isSmoothHerm_tensor hsQ (DiagRAux.isSmoothHerm_tensor hsLL hsLL)
  have aT2 : T2.a = 0 := by
    funext k
    have := hdeg k
    simp only [hT2, hQ, hLL, HermLine.tensor, halfInvLine, Pi.add_apply, Pi.zero_apply]
    linarith
  have hT2h : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → T2.h z = 1 := by
    intro z hz
    have hpos : 0 < X₀.h z * X₁.h z := mul_pos (X₀.pos z hz) (X₁.pos z hz)
    simp only [hT2, hQ, hLL, HermLine.tensor]
    rw [halfInvLine_h_of_pos _ _ _ _ z hz, ← Real.rpow_add hpos]
    norm_num
    rw [Real.rpow_neg_one]
    exact mul_inv_cancel₀ hpos.ne'
  set G : HermLine ι → HermLine ι → ℝ :=
    fun A B => I P (n + 2) (Fin.snoc (Fin.cons A L : Fin (n + 1) → HermLine ι) B) with hG
  have G_add : ∀ {A B C'}, IsSmoothHerm A → IsSmoothHerm B → IsSmoothHerm C' →
      G A (B.tensor C') = G A B + G A C' := fun hA hB hC =>
    hF.2.1 P (n + 1) _ _ _ hW (smooth_cons hA hL) hB hC
  have G_symm : ∀ {A B}, IsSmoothHerm A → IsSmoothHerm B → G A B = G B A := by
    intro A B hA hB
    have := hF.1 P (n + 2) (Fin.snoc (Fin.cons B L : Fin (n + 1) → HermLine ι) A)
      (Equiv.swap 0 (Fin.last (n + 1))) hW (smooth_snoc hA (smooth_cons hB hL))
    rw [snoc_cons_comp_swap] at this
    exact this
  have e6 : ∀ {M}, IsSmoothHerm M → G M X₀ + G M X₁ + G M LL + G M LL = 0 := by
    intro M hsM
    rw [← G_add hsM hs0 hs1, add_assoc, ← G_add hsM hsLL hsLL,
      ← G_add hsM hsQ (DiagRAux.isSmoothHerm_tensor hsLL hsLL)]
    exact I_snoc_triv hF hW (smooth_cons hsM hL) hsT2 aT2 fun z hz => hT2h z hz.1
  have e0 := e6 hs0
  have e1 := e6 hs1
  have e5 : G X₀ X₁ = G X₁ X₀ := G_symm hs0 hs1
  have r0 : I P (n + 2) (Fin.cons X₀ (Fin.cons X₀ L)) = G X₀ X₀ :=
    cons_eq_snoc hF hW (smooth_cons hs0 hL) hs0
  have r1 : I P (n + 2) (Fin.cons X₁ (Fin.cons X₁ L)) = G X₁ X₁ :=
    cons_eq_snoc hF hW (smooth_cons hs1 hL) hs1
  rw [r0, r1]
  show G X₀ X₀ - G X₁ X₁ = -2 * (G X₀ LL - G X₁ LL)
  linarith

end PositivityTheory.Xgp.sq_R

theorem PositivityTheory.Xgp.t_sq_R : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2) (Xi : HermLine ι) (X₀ X₁ : HermLine Q.ιW), Xi.a = xi2 → IsSmoothHerm Xi → IsPullHerm (Q.κ 0) (Q.v 0) Xi X₀ → IsPullHerm (Q.κ 1) (Q.v 1) Xi X₁ → ∀ T : Fin (d + 1) → HermLine Q.ιW, (∀ j, IsSmoothHerm (T j)) → II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons X₀ (Fin.cons X₀ T)) - II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons X₁ (Fin.cons X₁ T)) = 2 * (ptsIntegral Q.PW (pot (Fin.cons X₀ T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) := by
  intro hIn II hII K _ ι _ P d k₀ xi2 Q Xi X₀ X₁ hXa hX hp0 hp1 T hT
  have hF : IsIntersectionFamily (II Q.KW Q.ιW) := hII.1 Q.KW Q.ιW
  have hW : IsArithVar Q.PW (d + 3) := Q.arithW
  have hWp : Q.PW.IsPrime := hW.2.1.1
  have hs0 : IsSmoothHerm X₀ := PositivityTheory.Xgp.sq_R.smooth_pull (Q.block 0) hX hp0
  have hs1 : IsSmoothHerm X₁ := PositivityTheory.Xgp.sq_R.smooth_pull (Q.block 1) hX hp1
  have hdeg : ∀ k, 2 * ((Q.dg k : ℤ) - Q.dh k) = -(X₀.a k + X₁.a k) := by
    intro k
    rw [hp0.1, hp1.1, hXa]
    exact Q.deg_eq k
  set LL := GroundTheory.Heights₂.Heights.Inter.DiagRAux.halfInvLine X₀ X₁ (fun k => (Q.dg k : ℤ) - Q.dh k) hdeg with hLL
  have hsLL : IsSmoothHerm LL := GroundTheory.Heights₂.Heights.Inter.DiagRAux.isSmoothHerm_halfInvLine hs0 hs1 _ hdeg
  have hrat : IsRatSectionOn Q.PW LL Q.g Q.h :=
    ⟨_, _, Q.g_deg, Q.h_deg, Q.g_nmem, Q.h_nmem, fun k => rfl⟩
  have hdiv : ReciprocityTheory.ChartRestriction.G.AI.T.toZCycle (divCycle Q.PW Q.g) - ReciprocityTheory.ChartRestriction.G.AI.T.toZCycle (divCycle Q.PW Q.h) =
      Finsupp.single Q.Δ 1 := by
    classical
    ext W
    simp only [Q.div_eq, ReciprocityTheory.ChartRestriction.G.AI.T.toZCycle, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply,
      Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    split_ifs <;> push_cast <;> ring
  have key : ∀ A : HermLine Q.ιW, IsSmoothHerm A →
      II Q.KW Q.ιW Q.PW (d + 3) (Fin.snoc (Fin.cons A T : Fin (d + 2) → HermLine Q.ιW) LL) =
        II Q.KW Q.ιW Q.Δ (d + 2) (Fin.snoc T A) -
          ptsIntegral Q.PW (pot (Fin.cons A T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) := by
    intro A hA
    have e7 := hIn.ratR Q.KW Q.ιW (II Q.KW Q.ιW) hF Q.PW (d + 2) (Fin.cons A T) LL Q.g Q.h hW
      (GroundTheory.Heights₂.Heights.Inter.DiagRAux.smooth_cons hA hT) hsLL hrat
    have e8 := GroundTheory.Heights₂.Heights.Inter.DiagRAux.cycR_sub_eq (II Q.KW Q.ιW) Q.PW
      (Fin.cons A T : Fin (d + 2) → HermLine Q.ιW) Q.g Q.h Q.Δ hdiv Q.arithΔ.2.2.1
    have e9 := PositivityTheory.Xgp.sq_R.cons_eq_snoc hF Q.arithΔ hT hA
    have e10 : ptsIntegral Q.PW (pot (Fin.cons A T : Fin (d + 2) → HermLine Q.ιW)) (logNormRat LL Q.g Q.h) =
        ptsIntegral Q.PW (pot (Fin.cons A T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) := by
      refine GroundTheory.Heights₂.Heights.Inter.ZeroSetNull.proof Q.KW Q.ιW Q.PW (d + 2) (Q.g * Q.h) (Q.dg + Q.dh) _ _ _ hW
        (by classical exact GroundTheory.Heights₂.Heights.Inter.exHomog_mul Q.g_deg Q.h_deg)
        (fun hm => (hWp.mem_or_mem hm).elim Q.g_nmem Q.h_nmem) ?_
      intro z hz hne
      have hz' := hz.1
      rw [map_mul, eval_mul] at hne
      have hgz : ‖eval z (map (Int.castRingHom ℂ) Q.g)‖ ≠ 0 := norm_ne_zero_iff.2 (left_ne_zero_of_mul hne)
      have hhz : ‖eval z (map (Int.castRingHom ℂ) Q.h)‖ ≠ 0 := norm_ne_zero_iff.2 (right_ne_zero_of_mul hne)
      have h0 := X₀.pos z hz'
      have h1 := X₁.pos z hz'
      unfold logNormRat AlgSq.logNormT
      rw [← hp0.2 z, ← hp1.2 z, hLL, GroundTheory.Heights₂.Heights.Inter.DiagRAux.halfInvLine_h_of_pos _ _ _ _ z hz',
        Real.log_div (div_ne_zero hgz hhz) (Real.rpow_pos_of_pos (mul_pos h0 h1) _).ne',
        Real.log_rpow (mul_pos h0 h1), Real.log_mul h0.ne' h1.ne']
      ring
    rw [e7, recRRat, e8, e9, e10]
  have hV := _root_.GlobalTheory.CompanionTheory.Ar.PB.lemma_v_lines hIn II hII Q.KW Q.ιW Q.Δ (d + 1) T X₀ X₁ ∅ (fun _ => 0) Q.arithΔ hT hs0 hs1
    (by simp) (PositivityTheory.Xgp.t_sq_diag K ι P d k₀ xi2 Q Xi X₀ X₁ hp0 hp1) (by simp)
  rw [Finset.sum_empty, zero_mul, abs_nonpos_iff] at hV
  have hsq := PositivityTheory.Xgp.sq_R.sq_sub hF (n := d + 1) hW hT hs0 hs1 _ hdeg
  have k0 := key X₀ hs0
  have k1 := key X₁ hs1
  rw [← hLL] at hsq
  linarith
end

