module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ProdTermAddPeriodTranslationLattice
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEvLePreimage
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecCoord

theorem germ_le_preimage (Γ : Germs) (w : ℂ) {Z : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ (spMap (Γ.ev w).toRingHom ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro q _
  let p : PrimeSpectrum (Γ.R w) := spMap (Γ.ev w).toRingHom (default : PrimeSpectrum ℂ)
  have hp : p ∈ (show Set (PrimeSpectrum (Γ.R w)) from (x ⁻¹ᵁ U).carrier) :=
    h (x := (default : PrimeSpectrum ℂ)) trivial
  have hle : (show PrimeSpectrum (Γ.R w) from q) ≤ p := by
    intro s hs
    by_contra hn
    refine (show PrimeSpectrum (Γ.R w) from q).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hs (Γ.unit w s fun h0 => hn ?_))
    show (Γ.ev w).toRingHom s ∈ (default : PrimeSpectrum ℂ).asIdeal
    rw [show (Γ.ev w).toRingHom s = 0 from h0]
    exact zero_mem _
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 hle).mem_open (x ⁻¹ᵁ U).isOpen hp

theorem comp_le_preimage {X Y Z : Scheme.{0}} (g : X ⟶ Y) (x : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (g ≫ x) ⁻¹ᵁ U := fun p _ => h (x := g p) trivial

theorem exists_ev_le_preimage {Z : Scheme.{0}} {T : ℝ} (yT : Sp (Conv.halfRing T) ⟶ Z) (U : Z.Opens)
    (hU : ⊤ ≤ (spMap (Conv.halfRing T).val.toRingHom ≫ yT) ⁻¹ᵁ U) :
    ∃ T' ≥ T, ∀ w : ℂ, T' < w.im → ∀ hw : T < w.im, ⊤ ≤ (spMap (Conv.ev T w hw).toRingHom ≫ yT) ⁻¹ᵁ U := by
  have hfac : spMap (Conv.halfRing T).val.toRingHom ≫ yT =
      spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫
        (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) := by
    rw [← Category.assoc, ← spMap_comp]
    rfl
  have hU' : ⊤ ≤ (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) ⁻¹ᵁ U := by
    intro p _
    rw [hfac] at hU
    obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
      Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
    exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial
  obtain ⟨T', h, hT'⟩ := Conv.exists_le_preimage_inclusion yT hU'
  refine ⟨T', h, fun w hw' hw => ?_⟩
  have e : (Conv.ev T w hw).toRingHom = (Conv.ev T' w hw').toRingHom.comp
      (Subalgebra.inclusion (Conv.halfRing_mono h) : Conv.halfRing T →+* Conv.halfRing T') :=
    RingHom.ext fun r => Conv.ev_congr hw hw' rfl
  rw [e, spMap_comp, Category.assoc]
  exact comp_le_preimage _ _ _ hT'

theorem spec_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), ∀ (N : ℕ) [NeZero N] (C : Coords Φ N), ∃ T' ≥ Ψ.T, ∃ hT : C.T ≤ T', ∀ w (hw : T' < w.im), ⊤ ≤ Ψ.yw w ⁻¹ᵁ C.U ∧ (∀ hw', ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw')).toRingHom ≫ Ψ.yT) ⁻¹ᵁ C.U) ∧ ∀ i v (x' : Sp ℂ ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme) (j : o.t.PP.L.ι), x' ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.pi w v).left → ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → valR x' ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) = Conv.ev C.T w (lt_of_le_of_lt hT hw) (C.cf i v) * Ψ.fr w j v ^ N := by
  intro E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ N _ C
  obtain ⟨T₁, hT₁, hU⟩ := exists_ev_le_preimage Ψ.yT C.U (by rw [Ψ.yT_gen]; exact C.mem)
  refine ⟨max T₁ C.T, le_max_of_le_left hT₁, le_max_right _ _, fun w hw => ?_⟩
  have hw1 : T₁ < w.im := (le_max_left _ _).trans_lt hw
  have hwC : C.T < w.im := (le_max_right _ _).trans_lt hw
  have hwT : Ψ.T < w.im := lt_of_le_of_lt hT₁ hw1
  have hy : ⊤ ≤ Ψ.yw w ⁻¹ᵁ C.U := by
    rw [Ψ.yw_eq w hwT]
    exact hU w hw1 hwT
  have hg : ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hwT)).toRingHom ≫ Ψ.yT) ⁻¹ᵁ C.U := by
    apply germ_le_preimage
    have e : (Γ.ev w).toRingHom.comp (Subalgebra.inclusion (Γ.le Ψ.T w hwT)).toRingHom =
        (Conv.ev Ψ.T w hwT).toRingHom := RingHom.ext fun r => Γ.ev_eq Ψ.T w hwT r
    rw [← Category.assoc, ← spMap_comp, e, ← Ψ.yw_eq w hwT]
    exact hy
  refine ⟨hy, fun _ => hg, fun i v x' j hx' hj => ?_⟩
  have hxU : ⊤ ≤ (Ψ.xt w hwT v).left ⁻¹ᵁ (o.t.G.hom ⁻¹ᵁ C.U) := by
    rw [← Scheme.Hom.comp_preimage, Over.w]
    exact hg
  have hxj : ⊤ ≤ (Ψ.xt w hwT v).left ⁻¹ᵁ o.t.PP.L.U j := by
    apply germ_le_preimage
    rw [← Ψ.pi_eq w hwT v]
    exact hj
  obtain ⟨z, hz⟩ : ∃ z : Sp (Γ.R w) ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme,
      z ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.xt w hwT v).left :=
    ⟨IsOpenImmersion.lift (o.t.G.hom ⁻¹ᵁ C.U).ι (Ψ.xt w hwT v).left (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hxU (x := p) trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hzj : ⊤ ≤ z ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j) := by
    intro p _
    rw [← hz] at hxj
    exact Set.mem_iInter.2 fun _ => hxj (x := p) trivial
  have ex : x' = spMap (Γ.ev w).toRingHom ≫ z := by
    rw [← cancel_mono (o.t.G.hom ⁻¹ᵁ C.U).ι, hx', Category.assoc, hz, Ψ.pi_eq w hwT v]
  have hgen : (spMap (Γ.R w).val.toRingHom ≫ z) ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Φ.x v).left := by
    rw [Category.assoc, hz, Ψ.xt_gen]
  have hv := C.val i v _ j hgen (by rw [← Ψ.xt_gen w hwT v]; exact comp_le_preimage _ _ _ hxj)
  rw [HolHom.valR_spMap _ _ _ hzj, ← Ψ.τt_gen w hwT v j hxj] at hv
  have hr : valR z ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) =
      Subalgebra.inclusion (Γ.le C.T w hwC) (C.cf i v) * Ψ.τt w v j ^ N := Subtype.ext hv
  rw [ex, HolHom.valR_spMap _ _ _ hzj, hr, map_mul, map_pow]
  exact congrArg (· * _) (Γ.ev_eq C.T w hwC (C.cf i v))

end GlobalTheory.SpecCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFormalConvergence
section
noncomputable section

namespace GlobalTheory.ArcPts

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

section
variable {O : Type} [CommRing O] [StarRing O] {A : AnArc O} {T : ℝ} (hT : A.IsConvLine T) {j : ℕ} [NeZero j]
include hT

theorem fsum_mem_halfRing {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (v : A.V) :
    ∃ hm : A.FSum j α th v ∈ Conv.halfRing T, ∀ w hw, Conv.ev T w hw ⟨_, hm⟩ = A.Sum j α th w v :=
  ⟨fun _ hw => (AnArc.hasSum_coeff_FSum hT h hw v).summable,
    fun _ hw => Conv.ev_eq_of_hasSum hw _ (AnArc.hasSum_coeff_FSum hT h hw v)⟩

theorem exists_dfsum_halfRing {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (z₀ : A.V) :
    ∃ F : Conv.halfRing T, IsDFSum A j α th z₀ F ∧
      ∀ w hw, Conv.ev T w hw F = fderiv ℂ (A.Sum j α th w) 0 z₀ := by
  let S : ℂ⸨X⸩ := HahnSeries.ofSuppBddBelow (fun n => fderiv ℂ (fun v => (A.FSum j α th v).coeff n) 0 z₀)
    ⟨-A.be α α, fun n hn => by
      by_contra hlt
      exact hn (by simp only [AnArc.fderiv_coeff_FSum_eq_zero (not_le.1 hlt), zero_apply])⟩
  exact ⟨⟨S, fun _ hw => (AnArc.hasSum_fderiv_coeff_FSum hT h hw 0 z₀).summable⟩, fun _ => rfl,
    fun _ hw => Conv.ev_eq_of_hasSum hw _ (AnArc.hasSum_fderiv_coeff_FSum hT h hw 0 z₀)⟩

theorem differentiable_ev_comb (f : A.V → Conv.halfRing T) (hf : IsComb A j (Conv.halfRing T) (fun v => f v))
    (w : ℂ) (hw : T < w.im) : Differentiable ℂ (fun v => Conv.ev T w hw (f v)) := by
  obtain ⟨n, r, α, th, h1, h2⟩ := hf
  have key : (fun v => Conv.ev T w hw (f v)) =
      fun v => ∑ i, Conv.ev T w hw ⟨r i, (h1 i).1⟩ * A.Sum j (α i) (th i) w v := by
    funext v
    choose hm hv using fun i => fsum_mem_halfRing hT (h1 i).2 v
    have e : f v = ∑ i, (⟨r i, (h1 i).1⟩ : Conv.halfRing T) * ⟨_, hm i⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact h2 v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hv i w hw]
  rw [key]
  exact Differentiable.fun_sum fun i _ =>
    (AnArc.differentiable_Sum hT (NeZero.ne j) (h1 i).2 hw).const_mul _

end

theorem exists_formal_convergence : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ (j : ℕ) [NeZero j], (∀ α, ∀ th ∈ A.Theta j α, (∀ v, ∃ h : A.FSum j α th v ∈ Conv.halfRing T, ∀ w hw, Conv.ev T w hw ⟨_, h⟩ = A.Sum j α th w v) ∧ ∀ z₀, ∃ F : Conv.halfRing T, IsDFSum A j α th z₀ F ∧ ∀ w hw, Conv.ev T w hw F = fderiv ℂ (A.Sum j α th w) 0 z₀) ∧ ∀ f : A.V → Conv.halfRing T, IsComb A j (Conv.halfRing T) (fun v => f v) → ∀ w hw, Differentiable ℂ (fun v => Conv.ev T w hw (f v)) := by
  intro O _ _ A
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  refine ⟨T₀, fun T hT j _ => ?_⟩
  have h := h₀.mono hT
  exact ⟨fun α th hth => ⟨fsum_mem_halfRing h hth, exists_dfsum_halfRing h hth⟩, differentiable_ev_comb h⟩

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsFactor
section
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem exists_isFactor : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∃ (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ), IsFactor A lin cst ∧ ∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la' := by
  intro O _ _ A
  refine ⟨fun _ la => A.lin la, A.logConst, fun w la v j α th h m => ?_, fun w la la' => ?_⟩
  · rw [A.term_add_period h w la m v, A.perFactor_eq_exp, A.L_apply]
  · rw [A.lin_Pw_sub]; ring

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNoCommonZero
section
noncomputable section

namespace GlobalTheory.SpanFrame

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped LaurentSeries PowerSeries

theorem exists_inverse_mem {k K : Type} [Field k] [Field K] [Algebra k K] (F : IntermediateField k K) {ι κ : Type}
    [Fintype ι] [DecidableEq κ] (c : κ → ι → K) (r : ι → κ → K) (hr : ∀ i l, r i l ∈ F)
    (h : ∀ a l, ∑ i, c a i * r i l = if a = l then 1 else 0) :
    ∃ c' : κ → ι → K, (∀ a i, c' a i ∈ F) ∧ ∀ a l, ∑ i, c' a i * r i l = if a = l then 1 else 0 := by
  obtain ⟨π, hπ⟩ := (Algebra.linearMap F K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap F K).injective)
  have h1 : π 1 = 1 := by simpa using LinearMap.congr_fun hπ 1
  refine ⟨fun a i => π (c a i), fun a i => (π _).2, fun a l => ?_⟩
  have e := congrArg (fun x => (π x : K)) (h a l)
  have e' : ∀ i, π (c a i * r i l) = (⟨r i l, hr i l⟩ : F) * π (c a i) := fun i => by
    rw [mul_comm (c a i)]; exact map_smul π (⟨r i l, hr i l⟩ : F) (c a i)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, e', apply_ite π, h1, map_zero] at e
  rw [IntermediateField.coe_sum] at e
  refine Eq.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _) (e.trans ?_)
  split_ifs <;> rfl

variable {O : Type} [CommRing O] [StarRing O] {A : AnArc O} {N : ℕ} [NeZero N]

theorem IsComb.mono {B B' : Set ℂ⸨X⸩} (h : B ⊆ B') {f : A.V → ℂ⸨X⸩} (hf : IsComb A N B f) : IsComb A N B' f :=
  let ⟨n, r, α, th, h1, h2⟩ := hf
  ⟨n, r, α, th, fun i => ⟨h (h1 i).1, (h1 i).2⟩, h2⟩

theorem exists_no_common_zero (hA : AnFin A) (hN : 2 ≤ N) {n : ℕ} {α : Fin n → A.X}
    {th : Fin n → (Fin A.gB → ℂ) → ℂ} (hth : ∀ i, th i ∈ A.Theta N (α i))
    (hli : LinearIndependent ℂ⸨X⸩ (fun i v => A.FSum N (α i) (th i) v))
    (hsp : ∀ α', ∀ th' ∈ A.Theta N α', ∃ r : Fin n → ℂ⸨X⸩, (∀ i T, r i ∈ Conv.halfRing T) ∧
      ∀ v, A.FSum N α' th' v = ∑ i, r i * A.FSum N (α i) (th i) v)
    {m : ℕ} (f : Fin m → A.V → ℂ⸨X⸩)
    (hf : ∀ i, ∃ T : ℝ, IsComb A N (Conv.halfRing T) (f i) ∧ ∀ v, f i v ∈ Conv.halfRing T)
    (hs : ∀ α', ∀ th' ∈ A.Theta N α', ∃ c : Fin m → ℂ⸨X⸩, ∀ v, A.FSum N α' th' v = ∑ i, c i * f i v) :
    ∃ (T : ℝ) (hm : ∀ i v, f i v ∈ Conv.halfRing T), (∀ i, IsComb A N (Conv.halfRing T) (f i)) ∧
      ∀ (w : ℂ) (hw : T < w.im) v, ∃ i, Conv.ev T w hw ⟨f i v, hm i v⟩ ≠ 0 := by
  classical
  choose T₁ hT₁ hT₁' using hf
  choose ρ hρ hρ' using hsp
  have hR : ∀ i, ∃ R : Fin n → ℂ⸨X⸩, (∀ l, R l ∈ Conv.convLaurent) ∧
      ∀ v, f i v = ∑ l, R l * A.FSum N (α l) (th l) v := fun i => by
    obtain ⟨p, r, β, t, h1, h2⟩ := hT₁ i
    refine ⟨fun l => ∑ a, r a * ρ (β a) (t a) (h1 a).2 l, fun l => sum_mem fun a _ => mul_mem
      (Conv.halfRing_le_convLaurent _ (h1 a).1) (Conv.halfRing_le_convLaurent 0 (hρ _ _ _ l 0)), fun v => ?_⟩
    rw [h2]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hρ' _ _ (h1 a).2 v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm
  choose R hR hR' using hR
  choose c hc using fun a => hs (α a) (th a) (hth a)
  have key : ∀ (c : Fin m → ℂ⸨X⸩) v, ∑ i, c i * f i v = ∑ l, (∑ i, c i * R i l) * A.FSum N (α l) (th l) v :=
    fun c v => by
      simp only [hR', Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
  obtain ⟨c', hc', hc''⟩ := exists_inverse_mem Conv.convLaurent c R hR fun a l =>
    Fintype.linearIndependent_iffₛ.1 hli (fun l => ∑ i, c a i * R i l) (fun l => if a = l then 1 else 0) (by
      funext v
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← key, ← hc]
      simp) l
  have hF : ∀ a v, A.FSum N (α a) (th a) v = ∑ i, c' a i * f i v := fun a v => by
    rw [key]
    simp [hc'']
  choose T₂ hT₂ using fun a i => Conv.mem_convLaurent_iff_halfRing.1 (hc' a i)
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  obtain ⟨B₁, hB₁⟩ := Finite.exists_le T₁
  obtain ⟨B₂, hB₂⟩ := Finite.exists_le (fun p : Fin n × Fin m => T₂ p.1 p.2)
  have l₀ : T₀ ≤ max T₀ (max B₁ B₂) := le_max_left _ _
  have l₁ : ∀ i, T₁ i ≤ max T₀ (max B₁ B₂) := fun i => (hB₁ i).trans ((le_max_left _ _).trans (le_max_right _ _))
  have l₂ : ∀ a i, T₂ a i ≤ max T₀ (max B₁ B₂) := fun a i =>
    (hB₂ (a, i)).trans ((le_max_right _ _).trans (le_max_right _ _))
  generalize max T₀ (max B₁ B₂) = T at l₀ l₁ l₂
  have hT := h₀.mono l₀
  refine ⟨T, fun i v => Conv.halfRing_mono (l₁ i) (hT₁' i v),
    fun i => IsComb.mono (Conv.halfRing_mono (l₁ i)) (hT₁ i), fun w hw v => ?_⟩
  obtain ⟨t₁, ht₁, ht₁'⟩ := hA.2
  obtain ⟨β, t, ht, hne⟩ := A.exists_Sum_ne_zero_at hT ht₁ ht₁' hw hN v
  by_contra hz
  push Not at hz
  have hm : A.FSum N β t v ∈ Conv.halfRing T := fun _ hw => (AnArc.hasSum_coeff_FSum hT ht hw v).summable
  have e : (⟨_, hm⟩ : Conv.halfRing T) = ∑ a, ⟨_, hρ β t ht a T⟩ * ∑ i,
      (⟨_, Conv.halfRing_mono (l₂ a i) (hT₂ a i)⟩ : Conv.halfRing T) *
        ⟨f i v, Conv.halfRing_mono (l₁ i) (hT₁' i v)⟩ := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, ← hF]
    exact hρ' β t ht v
  refine hne ((Conv.ev_eq_of_hasSum hw ⟨_, hm⟩ (AnArc.hasSum_coeff_FSum hT ht hw v)).symm.trans ?_)
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hz, mul_zero, Finset.sum_const_zero]

end GlobalTheory.SpanFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueLiftCoordsLocalSubring
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.LiftPoint

open GlobalTheory.Points GlobalTheory.AmpleSpan GlobalTheory.Specialise

section General

variable {A K : Type} [CommRing A] [CommRing K] {j : A →+* K} {X Y : Scheme.{0}} {f : X ⟶ Y} {H : LB X}
  {I : Type} {t : I → LB.Sec H}

theorem exists_lift_of_valR_mem (hj : Function.Injective j) {D : X.Opens} (hD : IsAffineOpen D) (x : Sp K ⟶ X)
    (hx : ⊤ ≤ x ⁻¹ᵁ D) (h : ∀ g, valR x D g ∈ j.range) :
    ∃ ξ : Sp A ⟶ X, ⊤ ≤ ξ ⁻¹ᵁ D ∧ spMap j ≫ ξ = x := by
  choose φ hφ using h
  simp only [valR_eq x D hx] at hφ
  let ψ : Γ(X, D) →+* A := ⟨⟨⟨φ, hj (by simp [hφ])⟩, fun a b => hj (by simp [hφ])⟩, hj (by simp [hφ]),
    fun a b => hj (by simp [hφ])⟩
  refine ⟨_, le_preimage_specMap_fromSpec hD (CommRingCat.ofHom ψ), ?_⟩
  rw [← specMap_valMap_fromSpec hD x hx, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext hφ)

theorem ext_of_spMap_comp [IsAffine Y] (hj : Function.Injective j) {ξ ξ' : Sp A ⟶ Y}
    (h : spMap j ≫ ξ = spMap j ≫ ξ') : ξ = ξ' :=
  ext_of_valR (isAffineOpen_top Y) (le_preimage_top _) (le_preimage_top _) fun g => hj (by
    rw [← valR_spMap_comp j ξ ⊤ (le_preimage_top _), ← valR_spMap_comp j ξ' ⊤ (le_preimage_top _), h])

theorem exists_lift [IsAffine Y] [IsLocalRing A] (ht : EmbedsBy f t) (hj : Function.Injective j) {b : Sp A ⟶ Y}
    {x : Sp K ⟶ X} (hb : x ≫ f = spMap j ≫ b) {c : I → A} (h : HasCoords x t fun l => j (c l)) {m : I}
    (hm : IsUnit (c m)) : ∃ ξ : Sp A ⟶ X, ξ ≫ f = b ∧ spMap j ≫ ξ = x ∧ HasCoords ξ t c := by
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hx := h.le_nonzeroLocus (hm.map j)
  obtain ⟨ξ, hξ, e⟩ := exists_lift_of_valR_mem hj hD x hx fun g => by
    obtain ⟨q, rfl⟩ := hsurj g
    rw [valR_eval₂Hom f x hx]
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C, ← valR_eq, hb, valR_spMap_comp j b ⊤ (le_preimage_top _)]
      exact ⟨_, rfl⟩
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p l hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      refine mul_mem hp ⟨c l * hm.unit⁻¹.val, (hm.map j).mul_right_cancel ?_⟩
      rw [h.valR_ratio hx (hρ l), ← map_mul, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
  refine ⟨ξ, ext_of_spMap_comp hj ?_, e, ?_⟩
  · rw [← Category.assoc, e, hb]
  · have e' : (fun l => valR ξ (Out.nonzeroLocus (t m)) (ρ l) * c m) = c := funext fun l => hj (by
      rw [map_mul, ← valR_spMap_comp j ξ _ hξ, e]
      exact h.valR_ratio hx (hρ l))
    rw [← e']
    exact (hasCoords_ratio hξ hρ).mul_unit hm

end General

theorem le_preimage_powOver {S : Scheme.{0}} (G : Over S) (L : LB G.left) (U : S.Opens) (N : ℕ) {A : Type}
    [CommRing A] (x : Sp A ⟶ (G.hom ⁻¹ᵁ U).toScheme) {j : L.ι} (h : ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j) :
    ⊤ ≤ x ⁻¹ᵁ (Out.powOver G L U N).U (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => h hz

theorem existsUnique_lift : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (L : LB G.left) (U : S.Opens) (N n : ℕ) (b : Fin n → LB.Sec (Out.powOver G L U N)) (R K : Type) [CommRing R] [IsLocalRing R] [CommRing K] [IsLocalRing K] (f : R →+* K) (y : Sp R ⟶ S) (x : Sp K ⟶ (G.hom ⁻¹ᵁ U).toScheme) (cf : Fin n → R) (j : L.ι) (u : Kˣ), L.IsLB → IsAffineOpen U → AmpleSpan.EmbedsBy (G.hom ∣_ U) b → Function.Injective f → ⊤ ≤ y ⁻¹ᵁ U → x ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = spMap f ≫ y → ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → (∀ i, valR x ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = f (cf i) * u) → (∃ i, IsUnit (cf i)) → ∃! x' : Sp R ⟶ (G.hom ⁻¹ᵁ U).toScheme, x' ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y ∧ spMap f ≫ x' = x ∧ ∀ j', ⊤ ≤ (x' ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j' → ∃ u' : Rˣ, ∀ i, valR x' ((Out.powOver G L U N).U (fun _ => j')) ((b i).f (fun _ => j')) = cf i * u' := by
  intro S G _ _ L U N n b R K _ _ _ _ f y x cf j u hL hU hb hf hy hxy hj hval ⟨m, hm⟩
  have : IsAffine U := hU
  let y' : Sp R ⟶ U.toScheme := IsOpenImmersion.lift U.ι y (by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨y z, hy trivial⟩, rfl⟩)
  have ey : y' ≫ U.ι = y := IsOpenImmersion.lift_fac _ _ _
  have key : ∀ ξ : Sp R ⟶ (G.hom ⁻¹ᵁ U).toScheme,
      ξ ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y ↔ ξ ≫ G.hom ∣_ U = y' := fun ξ => by
    rw [← cancel_mono U.ι, ey, Category.assoc, morphismRestrict_ι]
  have hxy' : x ≫ G.hom ∣_ U = spMap f ≫ y' := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, ey, morphismRestrict_ι, hxy]
  obtain ⟨ξ, h₁, h₂, h₃⟩ := exists_lift hb hf hxy' (c := cf)
    ⟨fun _ => j, le_preimage_powOver G L U N x hj, u, hval⟩ hm
  refine ⟨ξ, ⟨(key ξ).2 h₁, h₂, fun j' hj' => h₃.chart (le_preimage_powOver G L U N ξ hj')⟩, ?_⟩
  rintro ξ' ⟨k₁, -, k₃⟩
  obtain ⟨j', hj'⟩ := exists_le_preimage_of_iSup_eq_top (ξ' ≫ (G.hom ⁻¹ᵁ U).ι) hL.cover
  exact HasCoords.ext hb (((key ξ').1 k₁).trans h₁.symm)
    ⟨fun _ => j', le_preimage_powOver G L U N ξ' hj', k₃ j' hj'⟩ h₃ hm

end GlobalTheory.LiftPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FderivTorusCoordinateRatioEqZeroOfTangent
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

namespace GlobalTheory.AbelianLetters

theorem fderiv_eq_zero_of_smul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {F u G : V → ℂ} {c : ℂ} {z : V}
    (hc : c ≠ 0) (hu : DifferentiableAt ℂ u 0) (hu0 : u 0 = 1) (hG : DifferentiableAt ℂ G 0) (hG0 : G 0 ≠ 0)
    (h : (fun t => F (c • t)) =ᶠ[nhds 0] fun t => u t * G t) (e : fderiv ℂ F 0 z = c⁻¹ * fderiv ℂ G 0 z) :
    fderiv ℂ u 0 z = 0 := by
  have e' := congrArg (· z) (h.fderiv_eq (𝕜 := ℂ))
  rw [fderiv_comp_smul, smul_zero, fderiv_fun_mul hu hG, hu0] at e'
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul, _root_.one_mul] at e'
  rw [e, ← _root_.mul_assoc, mul_inv_cancel₀ hc, _root_.one_mul, left_eq_add, mul_eq_zero] at e'
  exact e'.resolve_left hG0

theorem fderiv_ratio_eq_zero : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt), (∀ Tt b, (sB Tt b).b = b ^ n) → (∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b'))) → (∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b))) → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → 0 < n → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u → (∀ x, DifferentiableAt ℂ (u x) 0) → (∀ x, u x 0 = 1) → ∀ (v : epsR ℂ ⟶ D.P.A) (ν : Out.GtPt D (epsR ℂ)) (z : Fin g → ℂ), Out.GtPt.IsPull (spMap (epsScaleR ((n : ℂ)⁻¹))) (sB (epsR ℂ) v) ν → IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) z v.left → (∀ x j, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφT D (epsR ℂ) ν.b x) j → valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val = TrivSqZeroExt.inl (chiVal (ex 0) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (ex z) x j) 0 z)) → ∀ x, fderiv ℂ (u x) 0 z = 0 := by
  intro _ _ D g n ex sB hb _ hpull hadd hol _ hn u hu hud hu0 v ν z hν hv hval x
  have hv' := (HolHom.isDerivAt0_iff _ _ _).1 hv
  have hH := HolHom.holAt_of_isHolTo hol (Set.mem_univ 0)
  have hp := hpull _ _ v (𝟙 _)
  rw [Category.comp_id] at hp
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ (show Sp ℂ ⟶ _ from (ex 0).b.left) ⁻¹ᵁ
      LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A (sB D.P.A (𝟙 _)).b x) j := by
    choose j hj using fun k => exists_chart D.P.isLB (Out.DegPre.gtφT D D.P.A (sB D.P.A (𝟙 _)).b x k
      ((show Sp ℂ ⟶ _ from (ex 0).b.left) (default : PrimeSpectrum ℂ)))
    exact ⟨j, (HolHom.le_preimage_iff _ _).2 (Set.mem_iInter.2 hj)⟩
  have hvW := (HolHom.le_preimage_dual_iff hv'.1 _).2 hj
  have h1 := (top_le_wchart_pull hp.1 x j).2 hvW
  have h2 := (top_le_wchart_pull hν.1 x j).2 (fun p _ => h1 trivial)
  have e1 := valR_of_isPull hν x j
  have e2 := valR_of_isPull hp x j
  have e3 := HolHom.valR_spMap (epsScaleR ((n : ℂ)⁻¹)) (𝟙 (Sp (DualNumber ℂ)))
    (LB.wchart D.P.L (Out.DegPre.gtφT D (epsR ℂ) (sB (epsR ℂ) v).b x) j) h1 (((sB (epsR ℂ) v).s x).s j).val
  rw [Category.comp_id] at e3
  have e4 := congrArg TrivSqZeroExt.snd ((hval x j h2).symm.trans (e1.trans (e3.trans (congrArg _ e2))))
  have e5 : ∀ a : DualNumber ℂ, TrivSqZeroExt.snd (epsScaleR ((n : ℂ)⁻¹) a) = (n : ℂ)⁻¹ * TrivSqZeroExt.snd a := by
    intro a
    simp [epsScaleR]
  replace e4 := e4.trans ((e5 _).trans (congrArg (_ * ·) (hv'.2 _ hj _)))
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at e4
  obtain ⟨hev, hd⟩ := hH _ hj
  exact fderiv_eq_zero_of_smul (F := fun z' => chiVal (ex z') x j) (Nat.cast_ne_zero.2 hn.ne') (hud x) (hu0 x)
    (hd (((sB D.P.A (𝟙 _)).s x).s j).val)
    ((HolHom.valR_eq _ _ hj _).trans_ne ((((sB D.P.A (𝟙 _)).s x).s j).isUnit.map (HolHom.evalHom _ _ hj)).ne_zero)
    (hev.mono fun z' hz' => hu x z' j ((top_le_wchart_nsmul hadd (hb _ _) z' x j).2 hz')) e4

end GlobalTheory.AbelianLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorPowScaleInvEq
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor CategoryTheory.MonObj

namespace GlobalTheory.AbelianLetters

theorem scale_tangent_pow (P : Out.PolAV (Sp ℂ)) (v : epsR ℂ ⟶ P.A) (n : ℕ) (hn : 0 < n) (hv : IsTangent v) :
    spMap (epsScaleR ((n : ℂ)⁻¹)) ≫ (v ^ n).left = v.left := by
  have h : GrpTangent.epsScale ((n : ℂ)⁻¹) ≫ (v ^ n) = v := by
    rw [GrpTangent.pow_eq_epsScale_comp hv, GrpTangent.epsScale_mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'),
      GrpTangent.epsScale_one, Category.id_comp]
  exact congrArg (fun φ => φ.left) h

end GlobalTheory.AbelianLetters
end
end

