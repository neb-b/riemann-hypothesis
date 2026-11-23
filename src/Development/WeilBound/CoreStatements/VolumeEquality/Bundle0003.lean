module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0002
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0001
public import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsPoint
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifDefs
section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

def VecAt {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R : (Fin n → ℂ) → RiemLat E g Λ) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (t₀ : Fin n → ℂ) : Prop :=
  ∀ (m : ℕ) (s : Fin m → 𝔐.Li), (∀ a, ∃ v, 𝔐.M.ValAt (z t₀) (s a) v) →
    ∃ x : Fin m → (Fin n → ℂ) → Fin g → ℂ, (∀ a, AnalyticAt ℂ (x a) t₀) ∧ ∀ᶠ t in 𝓝 t₀, ∃ v : Fin m → (epsAt (z t) ⟶ 𝔐.t.G),
      (∀ a, 𝔐.M.ValAt (z t) (s a) (v a)) ∧ FibreLatVec 𝔐.t (z t) (R t) (fun a => x a t) v

structure KUnif (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n g : ℕ)
    (q : CMType H × Fin j × Fin j' ≃ Fin n) (κ : c.F →+* ℂ) where
  ι : Type
  fin : Finite ι
  Di : ι → Datum H
  sig : ∀ k, (Di k).p = D.p ∧ (Di k).q = D.q
  F : ∀ k, UnivFam E (CMType H) j j' n g (Di k).La
  q_eq : ∀ k, (F k).q = q
  form_eq : ∀ k, (F k).form = (Di k).EF ∨ (F k).form = -(Di k).EF
  σ_eq : ∀ k τ, (F k).σ τ = κ.comp (labelEmb c (sm τ))
  Γ : ∀ k, Subgroup ((Di k).La ≃ₗ[𝓞 E] (Di k).La)
  mem_Γ : ∀ k γ, γ ∈ Γ k ↔ InLevel l (Di k) γ
  arith : ∀ k, (F k).IsArith (Γ k)
  pt : ι → (Fin n → ℂ) → (Sp ℂ ⟶ Y.X)
  hol : ∀ k, IsHolTo (ballDom q) (pt k)
  comp_s_eq_spMap_of_isOver : ∀ k, ∀ t ∈ ballDom q, pt k t ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))
  interior : ∀ k, ∀ t ∈ ballDom q, centre (pt k t) ∈ abLocus Y.t.G
  disj : ∀ k k', ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, pt k t = pt k' t' → k = k'
  fibre : ∀ k, ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, pt k t = pt k t' ↔ (F k).Eqv (Γ k) t t'
  onto : ∀ p : Sp ℂ ⟶ Y.X, centre p ∈ abLocus Y.t.G → p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) →
    ∃ k, ∃ t ∈ ballDom q, pt k t = p
  lat : ∀ k, ∀ t ∈ ballDom q, FibreLat Y.t (pt k t) ((F k).R t)
  vec : ∀ (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (k : ι) (V : Set (Fin n → ℂ)) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)), IsOpen V → V ⊆ ballDom q →
    IsHolTo V z → (∀ t ∈ V, z t ≫ 𝔐.f = pt k t) → ∀ t₀ ∈ V, VecAt 𝔐 (F k).R z t₀
  locc : ∀ (m : ℕ) (T : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Y.X)), IsOpen T → IsPreconnected T → IsHolTo T y →
    (∀ b ∈ T, centre (y b) ∈ abLocus Y.t.G) → (∀ b ∈ T, y b ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))) →
    ∀ b ∈ T, ∀ b' ∈ T, ∀ k k', ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, y b = pt k t → y b' = pt k' t' → k = k'

def VecOfPeriods : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (κ : c.F →+* ℂ) (σ : KA l →+* ℂ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (n : ℕ) (V : Set (Fin n → ℂ))
    (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (xF : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c))
    (R : (Fin n → ℂ) → RiemLat E g (FU.Di i).La) (P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ)))
    (h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen V → IsHolTo V z → IsHolTo V xF → IsHolPeriods (FU.Di i) ty V P →
    (∀ a b, DifferentiableOn ℂ (fun t => h t a b) V) →
    (∀ t ∈ V, (R t).form = (FU.Di i).EF ∧ IsUnit (h t).det ∧ (∀ x, P t x = h t *ᵥ (R t).P x) ∧
      xF t ≫ Y.j = z t ≫ 𝔐.f ∧ xF t ≫ pullback.fst _ _ = FU.u i (P t) ∧ xF t ≫ pullback.snd _ _ = spMap κ) →
    ∀ t₀ ∈ V, VecAt 𝔐 R z t₀

def KUnifConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n g : ℕ)
    (q : CMType H × Fin j × Fin j' ≃ Fin n) (κ : c.F →+* ℂ),
    Nonempty (KUnif Y sm j j' n g q κ) → Nonempty (KUnif Y sm j j' n g q ((starRingEnd ℂ).comp κ))

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.ChartMeets
section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar

theorem trdeg_of_arithVar {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)} {n : ℕ}
    (h : IsArithVar P (n + 1)) : Algebra.trdeg ℤ (MRing J ⧸ P) = ((n + Fintype.card K : ℕ) : Cardinal) := by
  obtain ⟨_, ⟨hP, _, _⟩, hhor, hdim⟩ := h
  haveI := hP
  have hinj : Function.Injective (algebraMap ℤ (MRing J ⧸ P)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : (MvPolynomial.C a : MRing J) ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have hc : algebraMap ℤ (MRing J ⧸ P) a = Ideal.Quotient.mk P (MvPolynomial.C a) := by simp
      rw [← hc]
      exact ha
    have hc : a ∈ Ideal.comap (MvPolynomial.C : ℤ →+* MRing J) P := hmem
    rw [hhor] at hc
    exact (Submodule.mem_bot _).1 hc
  have hd := GroundTheory.Heights₂.Heights.IntDomainDim.proof (MRing J ⧸ P) hinj
  rw [hd] at hdim
  have h4 : (Cardinal.toENat (Algebra.trdeg ℤ (MRing J ⧸ P)) + 1 : ℕ∞)
      = ((n + Fintype.card K : ℕ) : ℕ∞) + 1 := by
    rw [show n + 1 + Fintype.card K = n + Fintype.card K + 1 by ring] at hdim
    exact_mod_cast hdim
  have h3 : Cardinal.toENat (Algebra.trdeg ℤ (MRing J ⧸ P)) = ((n + Fintype.card K : ℕ) : ℕ∞) :=
    WithTop.add_right_cancel ENat.one_ne_top h4
  exact Cardinal.toENat_eq_natCast.1 h3

theorem chartMeets : ChartMeets := by
  intro X Ω _ _ ξ K _ J _ y n Bd χ U htie hspec harith hU
  haveI : (mCoordIdeal y).IsPrime := harith.2.1.1
  have hhom : IsMultiHomogIdeal (mCoordIdeal y) := harith.2.1.2.1
  have hconv : ∀ (w : (k : K) × J k → ℂ) (f : MvPolynomial ((k : K) × J k) ℤ),
      aeval w f = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) := by
    intro w f
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]
  have hscale : ∀ (c : K → ℂ) (w : (k : K) × J k → ℂ) (s : MvPolynomial ((k : K) × J k) ℤ)
      (a : K → ℕ), IsMultiHomog s a → aeval (torusSmul c w) s = (∏ k, c k ^ a k) * aeval w s := by
    intro c w s a hs
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hprod : ∏ i, (torusSmul c w i) ^ d i = (∏ k, c k ^ a k) * ∏ i, w i ^ d i := by
      simp only [torusSmul, mul_pow, Finset.prod_mul_distrib]
      congr 1
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show ∏ j : J k, c k ^ d ⟨k, j⟩ = c k ^ a k
      rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
    rw [hprod]
    ring
  have htor : ∀ (c : K → ℂ) (w : (k : K) × J k → ℂ), w ∈ mcPts (mCoordIdeal y) →
      ∀ f ∈ mCoordIdeal y, aeval (torusSmul c w) f = 0 := by
    intro c w hw f hf
    obtain ⟨S, hS, hPS⟩ := hhom
    have hf' : f ∈ Ideal.span S := by
      rw [← hPS]
      exact hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨a, ha⟩ := hS s hs
      have hsP : s ∈ mCoordIdeal y := by
        rw [hPS]
        exact Ideal.subset_span hs
      rw [hscale c w s a ha, hconv, hw.2 s hsP, mul_zero]
    | zero => simp
    | add f₁ f₂ _ _ h₁ h₂ => rw [map_add (f := _), h₁, h₂, add_zero]
    | smul r f₁ _ h₁ => rw [smul_eq_mul, map_mul, h₁, mul_zero]
  obtain ⟨g, hg, hgU⟩ := SheetDecomposition.ChartForm.exists_form htie U hU
  have h0b : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  let D := fderiv ℂ χ.γ 0
  let Γ : (Fin n → ℂ) × (K → ℂ) → (k : K) × J k → ℂ :=
    fun w => torusSmul (fun k => 1 + w.2 k) (χ.γ w.1)
  let L : ((Fin n → ℂ) × (K → ℂ)) →L[ℂ] ((k : K) × J k → ℂ) :=
    ContinuousLinearMap.pi fun p : (k : K) × J k =>
      (ContinuousLinearMap.proj p).comp (D.comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (K → ℂ)))
      + χ.γ 0 p • (ContinuousLinearMap.proj p.1).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))
  have hγ : HasStrictFDerivAt χ.γ D 0 := (χ.analytic 0 h0b).hasStrictFDerivAt
  have hstrict : HasStrictFDerivAt Γ L 0 := by
    rw [hasStrictFDerivAt_pi']
    intro p
    have h1 : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => (1 : ℂ) + w.2 p.1)
        ((ContinuousLinearMap.proj p.1).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))) 0 :=
      by
        have hs : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => w.2 p.1)
            ((ContinuousLinearMap.proj p.1).comp
              (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))) 0 :=
          ((ContinuousLinearMap.proj p.1).comp
            (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))).hasStrictFDerivAt
        exact hs.const_add (1 : ℂ)
    have h2 : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => χ.γ w.1 p)
        ((ContinuousLinearMap.proj p).comp (D.comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (K → ℂ)))) 0 :=
      by
        have hγp : HasStrictFDerivAt (fun t : Fin n → ℂ => χ.γ t p)
            ((ContinuousLinearMap.proj p).comp D) (0 : Fin n → ℂ) := hasStrictFDerivAt_pi'.1 hγ p
        have hfst : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => w.1)
            (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (K → ℂ)) 0 := hasStrictFDerivAt_fst
        exact hγp.comp (0 : (Fin n → ℂ) × (K → ℂ)) hfst
    refine (h1.mul h2).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [L] <;> ring
  have hinjL : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨v, d⟩ h0
    have hcomp : ∀ p : (k : K) × J k, D v p + χ.γ 0 p * d p.1 = 0 := by
      intro p
      have := congrFun h0 p
      simpa [L] using this
    have hv : v = 0 := by
      refine χ.immersion 0 h0b v ⟨fun k => -d k, ?_⟩
      funext p
      simp only [torusSmul]
      linear_combination hcomp p
    subst hv
    have hd : d = 0 := by
      funext k
      obtain ⟨i, hi⟩ := (χ.mem 0 h0b).1 k
      have := hcomp ⟨k, i⟩
      simp only [map_zero, Pi.zero_apply, zero_add] at this
      exact (mul_eq_zero.1 this).resolve_left hi
    rw [hd]
    rfl
  have hfin : Module.finrank ℂ ((Fin n → ℂ) × (K → ℂ)) = n + Fintype.card K := by simp
  have htr : Algebra.trdeg ℤ (MvPolynomial ((k : K) × J k) ℤ ⧸ mCoordIdeal y)
      ≤ ↑(Module.finrank ℂ ((Fin n → ℂ) × (K → ℂ))) :=
    (trdeg_of_arithVar harith).trans_le (le_of_eq (by rw [hfin]))
  have hN : ∀ᶠ w : (Fin n → ℂ) × (K → ℂ) in 𝓝 0,
      w.1 ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ k, 1 + w.2 k ≠ 0 := by
    refine Filter.Eventually.and ?_ (Filter.eventually_all.2 fun k => ?_)
    · exact (Metric.isOpen_ball.preimage continuous_fst).mem_nhds (by simpa using h0b)
    · exact (isOpen_ne_fun (continuous_const.add ((continuous_apply k).comp continuous_snd))
        continuous_const).mem_nhds (by simp)
  have hev : ∀ f ∈ mCoordIdeal y, ∀ᶠ w : (Fin n → ℂ) × (K → ℂ) in 𝓝 0, aeval (Γ w) f = 0 := by
    intro f hf
    filter_upwards [hN] with w hw
    exact htor _ _ (χ.mem _ hw.1) f hf
  have hne := SheetDecomposition.ChartAlg.not_eventually_zero (mCoordIdeal y) htr Γ 0 L hstrict hinjL hev g hg
  obtain ⟨w, hwN, hwg⟩ : ∃ w : (Fin n → ℂ) × (K → ℂ),
      (w.1 ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ k, 1 + w.2 k ≠ 0) ∧ aeval (Γ w) g ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (hN.mono fun w hw => hcon w hw)
  have hmem := χ.mem _ hwN.1
  obtain ⟨z, hsp, hco⟩ := SheetDecomposition.ChartForm.exists_point htie (Γ w)
    (fun k => by
      obtain ⟨i, hi⟩ := hmem.1 k
      exact ⟨i, (mul_ne_zero (hwN.2 k) hi).isUnit⟩)
    (fun f hf => htor _ _ hmem f hf)
  have hcU := hgU z (Γ w) hsp hco hwg
  have hcoord : CoordsAt ξ y z (χ.γ w.1) := by
    obtain ⟨_, hrel⟩ := hco
    refine ⟨fun k => ?_, fun k c' hu => ?_⟩
    · obtain ⟨i, hi⟩ := hmem.1 k
      exact ⟨i, hi.isUnit⟩
    · have hu' : IsUnit (Γ w ⟨k, c'⟩) := (hwN.2 k).isUnit.mul hu
      obtain ⟨hy, hr⟩ := hrel k c' hu'
      refine ⟨hy, fun i => ?_⟩
      obtain ⟨r, hval, hreq⟩ := hr i
      refine ⟨r, hval, ?_⟩
      have hreq' : (1 + w.2 k) * χ.γ w.1 ⟨k, i⟩ = r * ((1 + w.2 k) * χ.γ w.1 ⟨k, c'⟩) := hreq
      apply mul_left_cancel₀ (hwN.2 k)
      linear_combination hreq'
  refine ⟨w.1, hwN.1, z, hcoord, ?_⟩
  intro x _
  have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  rw [hx]
  exact hcU

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
section
noncomputable section

namespace SheetDecomposition.CovSch

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {X Y : Scheme.{0}} {F : Type} [Field F]

theorem top_le_iff (x : Sp F ⟶ X) (U : X.Opens) : ⊤ ≤ x ⁻¹ᵁ U ↔ centre x ∈ U :=
  ⟨fun h => h (show IsLocalRing.closedPoint F ∈ (⊤ : (Sp F).Opens) from trivial),
    fun h => (Scheme.preimage_eq_top_of_closedPoint_mem x h).ge⟩

def val (x : Sp F ⟶ X) (U : X.Opens) (h : centre x ∈ U) : Γ(X, U) →+* F :=
  (Scheme.stalkClosedPointTo x).hom.comp (X.presheaf.germ U (centre x) h).hom

theorem val_eq (x : Sp F ⟶ X) (U : X.Opens) (h : centre x ∈ U) (s : Γ(X, U)) :
    val x U h s = (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((x.appLE U ⊤ ((top_le_iff x U).2 h)).hom s) := by
  have := congrArg (fun φ => φ.hom s) (Scheme.germ_stalkClosedPointTo x U h)
  exact this

theorem valAt'_eq (p : Sp ℂ ⟶ X) (U : X.Opens) (h : centre p ∈ U) (s : Γ(X, U)) : valAt' p U s = val p U h s := by
  rw [val_eq, valAt', dite_eq_left ((top_le_iff p U).2 h)]
  rfl

theorem val_res (x : Sp F ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : centre x ∈ V) (s : Γ(X, U)) :
    val x V h ((X.presheaf.map (homOfLE hVU).op).hom s) = val x U (hVU h) s := by
  have := X.presheaf.germ_res_apply (homOfLE hVU) (centre x) h s
  exact congrArg (Scheme.stalkClosedPointTo x).hom this

theorem val_comp (x : Sp F ⟶ X) (f : X ⟶ Y) (U : Y.Opens) (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ U) (h : centre x ∈ W)
    (h' : centre (x ≫ f) ∈ U) (s : Γ(Y, U)) : val x W h ((f.appLE U W hW).hom s) = val (x ≫ f) U h' s := by
  rw [val_eq, val_eq, ← Scheme.Hom.appLE_comp_appLE x f U W ⊤ hW ((top_le_iff x W).2 h)]
  rfl

theorem val_congr {x x' : Sp F ⟶ X} (e : x = x') (U : X.Opens) (h : centre x ∈ U) (h' : centre x' ∈ U)
    (s : Γ(X, U)) : val x U h s = val x' U h' s := by
  subst e
  rfl

theorem val_spMap {F' : Type} [Field F'] (i : F →+* F') (x : Sp F ⟶ X) (U : X.Opens) (h : centre x ∈ U)
    (h' : centre (spMap i ≫ x) ∈ U) (s : Γ(X, U)) : val (spMap i ≫ x) U h' s = i (val x U h s) := by
  rw [val_eq, val_eq, ← Scheme.Hom.appLE_comp_appLE (spMap i) x U ⊤ ⊤ ((top_le_iff x U).2 h) le_rfl]
  have := congrArg (fun φ => φ.hom ((x.appLE U ⊤ ((top_le_iff x U).2 h)).hom s))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom i))
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at this
  exact this

theorem centre_spMap {F' : Type} [Field F'] (i : F →+* F') (x : Sp F ⟶ X) : centre (spMap i ≫ x) = centre x := by
  have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  show x (spMap i _) = x _
  congr 1
  exact Subsingleton.elim _ _

theorem eq_of_val {U : X.Opens} (hU : IsAffineOpen U) {x x' : Sp F ⟶ X} (h : centre x ∈ U) (h' : centre x' ∈ U)
    (e : ∀ s, val x U h s = val x' U h' s) : x = x' := by
  have e1 : x.appLE U ⊤ ((top_le_iff x U).2 h) = x'.appLE U ⊤ ((top_le_iff x' U).2 h') := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of F)).hom]
    ext s
    have := e s
    rw [val_eq, val_eq] at this
    exact this
  have a := hU.SpecMap_appLE_fromSpec x (isAffineOpen_top _) ((top_le_iff x U).2 h)
  have b := hU.SpecMap_appLE_fromSpec x' (isAffineOpen_top _) ((top_le_iff x' U).2 h')
  rw [e1, b, IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

theorem exists_of_hom {U : X.Opens} (hU : IsAffineOpen U) (χ : Γ(X, U) →+* F) :
    ∃ (x : Sp F ⟶ X) (h : centre x ∈ U), ∀ s, val x U h s = χ s := by
  let x : Sp F ⟶ X := Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec
  have h : centre x ∈ U := by
    have : centre x ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rwa [hU.range_fromSpec] at this
  refine ⟨x, h, fun s => ?_⟩
  rw [val_eq, ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom χ)) hU.fromSpec U ⊤ ⊤
    hU.fromSpec_preimage_self.ge le_rfl]
  have e1 : hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ ((Spec Γ(X, U)).presheaf.map_id _)).trans (Category.comp_id _)
  rw [e1]
  have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom s))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ))
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at this
  refine this.trans ?_
  exact congrArg χ (congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso Γ(X, U)).inv_hom_id)

variable {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genMap_germ' (q : Cpt ξ) (U : X.Opens) (hq : q.1 ∈ U) (hg : centre ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq s) = val ξ U hg s := RegAtRing.genMap_germ q U hq hg s

theorem val_injective (hξ : IsCptGen ξ) (U : X.Opens) (hg : centre ξ ∈ U) (hU : ∀ q ∈ U, genPt ξ ⤳ q) :
    Function.Injective (val ξ U hg) := by
  intro s s' e
  refine TopCat.Presheaf.section_ext X.sheaf U s s' fun q hq => ?_
  apply hξ.inj ⟨q, hU q hq⟩
  exact (genMap_germ' ⟨q, hU q hq⟩ U hq hg s).trans (e.trans (genMap_germ' ⟨q, hU q hq⟩ U hq hg s').symm)

theorem exists_open (hξ : IsCptGen ξ) (T : Set Ω) (hT : T.Finite) (U₁ : X.Opens) (h₁ : centre ξ ∈ U₁) :
    ∃ (U : X.Opens) (h : centre ξ ∈ U), U ≤ U₁ ∧ T ⊆ Set.range (val ξ U h) := by
  induction T, hT using Set.Finite.induction_on with
  | empty => exact ⟨U₁, h₁, le_rfl, Set.empty_subset _⟩
  | @insert a T _ _ ih =>
    obtain ⟨U, h, hU, hT⟩ := ih
    obtain ⟨g, rfl⟩ := hξ.bij.2 a
    obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq g
    refine ⟨U ⊓ V, ⟨h, hV⟩, inf_le_left.trans hU, Set.insert_subset ⟨_, val_res ξ inf_le_right _ s⟩ ?_⟩
    intro b hb
    obtain ⟨s', rfl⟩ := hT hb
    exact ⟨_, val_res ξ inf_le_left _ s'⟩

variable {z : Sp ℂ ⟶ X}

theorem valAt_sec (hz : genPt ξ ⤳ centre z) (U : X.Opens) (h : centre z ∈ U) (hg : centre ξ ∈ U) (s : Γ(X, U)) :
    ValAt ξ z (val ξ U hg s) (val z U h s) :=
  ⟨hz, X.presheaf.germ U (centre z) h s, genMap_germ' ⟨centre z, hz⟩ U h hg s, rfl⟩

theorem v_mul {a b : Ω} {r t : ℂ} (ha : ValAt ξ z a r) (hb : ValAt ξ z b t) : ValAt ξ z (a * b) (r * t) := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  obtain ⟨_, s', rfl, rfl⟩ := hb
  exact ⟨h, s * s', map_mul _ _ _, map_mul _ _ _⟩

theorem v_unique (hξ : IsCptGen ξ) {a : Ω} {r t : ℂ} (ha : ValAt ξ z a r) (hb : ValAt ξ z a t) : r = t := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  obtain ⟨_, s', e, rfl⟩ := hb
  rw [hξ.inj _ e]

theorem v_inv {a : Ω} {r : ℂ} (ha : ValAt ξ z a r) (hr : r ≠ 0) : a ≠ 0 ∧ ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  have hs : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (isUnit_iff_ne_zero.mpr hr)
  obtain ⟨u, rfl⟩ := hs
  exact ⟨(u.isUnit.map (genMap ξ ⟨centre z, h⟩)).ne_zero, h,
    ((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)),
    map_units_inv (genMap ξ ⟨centre z, h⟩) u, map_units_inv (Scheme.stalkClosedPointTo z).hom u⟩

theorem exists_frac {U : X.Opens} (hU : IsAffineOpen U) (x : Sp F ⟶ X) (h : centre x ∈ U)
    (g : X.presheaf.stalk (centre x)) : ∃ a b : Γ(X, U), val x U h b ≠ 0 ∧
      g * X.presheaf.germ U (centre x) h b = X.presheaf.germ U (centre x) h a := by
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (U := U) ⟨centre x, h⟩
  have := hU.isLocalization_stalk ⟨centre x, h⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (hU.primeIdealOf ⟨centre x, h⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk (centre x)) g
  have hu := IsLocalization.map_units (M := (hU.primeIdealOf ⟨centre x, h⟩).asIdeal.primeCompl)
    (X.presheaf.stalk (centre x)) s
  exact ⟨r, s.1, (hu.map (Scheme.stalkClosedPointTo x).hom).ne_zero, hrs⟩

variable {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω}

theorem coordsAt_of_val (c : ∀ k, J k) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) {w : (Σ k, J k) → ℂ}
    (hw : ∀ s, ValAt ξ z (y s / y ⟨s.1, c s.1⟩) (w s)) (hw1 : ∀ k, w ⟨k, c k⟩ = 1) : CoordsAt ξ y z w := by
  refine ⟨fun k => ⟨c k, by rw [hw1]; exact isUnit_one⟩, fun k c' hu => ?_⟩
  obtain ⟨h0, hr⟩ := v_inv (hw ⟨k, c'⟩) hu.ne_zero
  have hy' : y ⟨k, c'⟩ ≠ 0 := fun e => h0 (by rw [e, zero_div])
  refine ⟨hy', fun i => ⟨w ⟨k, i⟩ * (w ⟨k, c'⟩)⁻¹, ?_, ?_⟩⟩
  · have h1 := v_mul (hw ⟨k, i⟩) hr
    have h2 : y ⟨k, i⟩ / y ⟨k, c k⟩ * (y ⟨k, c'⟩ / y ⟨k, c k⟩)⁻¹ = y ⟨k, i⟩ / y ⟨k, c'⟩ := by
      have := hy k
      field_simp
    exact h2 ▸ h1
  · rw [inv_mul_cancel_right₀ hu.ne_zero]

theorem val_of_coordsAt (c : ∀ k, J k) {w : (Σ k, J k) → ℂ} (hw : CoordsAt ξ y z w) (hw1 : ∀ k, w ⟨k, c k⟩ = 1)
    (s : Σ k, J k) : ValAt ξ z (y s / y ⟨s.1, c s.1⟩) (w s) := by
  obtain ⟨k, i⟩ := s
  obtain ⟨r, hr, e⟩ := (hw.2 k (c k) (by rw [hw1]; exact isUnit_one)).2 i
  rw [hw1, mul_one] at e
  exact e ▸ hr

end SheetDecomposition.CovSch
end
end

