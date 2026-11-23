module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSurjectiveOfOmegaMapSurjectiveConnected
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.PDivGroup

theorem surjective_of_cotangentPullback_surjective_nilAug {k A B : Type} [Field k] [CommRing A] [CommRing B]
    [Bialgebra k A] [Bialgebra k B] [Module.Finite k A] (f : B →ₐc[k] A)
    (hA : ∀ a ∈ augIdeal k A, IsNilpotent a) (hf : Function.Surjective (cotMap f)) :
    Function.Surjective f := by
  set I := augIdeal k A with hIdef
  set J := augIdeal k B with hJdef
  have hfJ : ∀ b ∈ J, f b ∈ I := by
    intro b hb
    have hb' : counit (R := k) b = 0 := hb
    show counit (R := k) (f b) = 0
    rw [CoalgHomClass.counit_comp_apply]; exact hb'

  have step1 : ∀ x ∈ I, ∃ b ∈ J, x - f b ∈ I ^ 2 := by
    intro x hx
    obtain ⟨c, hc⟩ := hf (AugCot.d (counitAlgHom k A) x)
    obtain ⟨b0, rfl⟩ := AugCot.d_surjective _ c
    rw [cotMap_d] at hc
    set b := b0 - algebraMap k B (counit b0) with hb
    have hbJ : b ∈ J := by
      show counit (R := k) b = 0
      simp [hb]
    have hdb : AugCot.d (counitAlgHom k A) (f b) = AugCot.d (counitAlgHom k A) (f b0) := by
      rw [hb, map_sub, AlgHomClass.commutes, map_sub, AugCot.d_algebraMap, sub_zero]
    refine ⟨b, hbJ, ?_⟩
    have h1 : AugCot.d (counitAlgHom k A) (x - f b) = 0 := by
      rw [map_sub, hdb, ← hc, sub_self]
    have hmem : x - f b ∈ I := I.sub_mem hx (hfJ b hbJ)
    rw [AugCot.d_of_mem _ hmem, Ideal.toCotangent_eq_zero] at h1
    exact h1

  have step2 : ∀ m : ℕ, ∀ y ∈ I ^ (m + 1), ∃ b ∈ J ^ (m + 1), y - f b ∈ I ^ (m + 2) := by
    intro m
    induction m with
    | zero =>
      intro y hy
      rw [zero_add, pow_one] at hy
      obtain ⟨b, hb, h⟩ := step1 y hy
      exact ⟨b, by rwa [zero_add, pow_one], h⟩
    | succ m ih =>
      intro y hy
      rw [pow_succ'] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro x hx z hz
        obtain ⟨b1, hb1, hu⟩ := step1 x hx
        obtain ⟨b2, hb2, hv⟩ := ih z hz
        have hfb1 : f b1 ∈ I := hfJ b1 hb1
        have hfb2 : f b2 ∈ I ^ (m + 1) := by
          have : f b2 = z - (z - f b2) := by ring
          rw [this]
          exact (I ^ (m + 1)).sub_mem hz (Ideal.pow_le_pow_right (by omega) hv)
        refine ⟨b1 * b2, ?_, ?_⟩
        · rw [pow_succ']; exact Ideal.mul_mem_mul hb1 hb2
        · set u := x - f b1
          set v := z - f b2
          have hx' : x = f b1 + u := by simp [u]
          have hz' : z = f b2 + v := by simp [v]
          have : x * z - f (b1 * b2) = f b1 * v + u * f b2 + u * v := by
            rw [hx', hz', map_mul]; ring
          rw [this]
          refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
          · rw [show m + 1 + 2 = 1 + (m + 2) by omega, pow_add, pow_one]
            exact Ideal.mul_mem_mul hfb1 hv
          · rw [show m + 1 + 2 = 2 + (m + 1) by omega, pow_add]
            exact Ideal.mul_mem_mul hu hfb2
          · rw [show m + 1 + 2 = 1 + (m + 2) by omega, pow_add, pow_one]
            exact Ideal.mul_mem_mul (Ideal.pow_le_self (by norm_num) hu) hv
      · rintro y1 y2 ⟨b1, hb1, h1⟩ ⟨b2, hb2, h2⟩
        refine ⟨b1 + b2, Ideal.add_mem _ hb1 hb2, ?_⟩
        have : y1 + y2 - f (b1 + b2) = (y1 - f b1) + (y2 - f b2) := by rw [map_add (f := _)]; ring
        rw [this]; exact Ideal.add_mem _ h1 h2
  have step3 : ∀ m : ℕ, ∀ x ∈ I, ∃ b : B, x - f b ∈ I ^ (m + 1) := by
    intro m
    induction m with
    | zero => intro x hx; exact ⟨0, by rw [map_zero, sub_zero, zero_add, pow_one]; exact hx⟩
    | succ m ih =>
      intro x hx
      obtain ⟨b, hb⟩ := ih x hx
      obtain ⟨b', -, hb'⟩ := step2 m _ hb
      refine ⟨b + b', ?_⟩
      have : x - f (b + b') = x - f b - f b' := by rw [map_add (f := _)]; ring
      rw [this]; exact hb'

  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  have hnil : IsNilpotent I := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian I)).2 ?_
    intro a ha
    exact (mem_nilradical).2 (hA a ha)
  obtain ⟨N, hN⟩ := hnil
  have hI : ∀ x ∈ I, ∃ b : B, f b = x := by
    intro x hx
    obtain ⟨b, hb⟩ := step3 N x hx
    have : x - f b ∈ I ^ N := Ideal.pow_le_pow_right (by omega) hb
    rw [hN] at this
    exact ⟨b, (sub_eq_zero.1 ((Submodule.mem_bot _).1 this)).symm⟩
  intro a
  have ha : a - algebraMap k A (counit a) ∈ I := by
    show counit (R := k) (a - algebraMap k A (counit a)) = 0
    simp
  obtain ⟨b, hb⟩ := hI _ ha
  refine ⟨b + algebraMap k B (counit a), ?_⟩
  rw [map_add (f := _), AlgHomClass.commutes, hb, sub_add_cancel]

theorem app_surjective_of_omegaMap_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), G.IsConn → Function.Surjective (omegaMap G H q) → ∀ n, Function.Surjective (q.app n) := by
  intro p _ k _ _ G H q hG hq n
  refine surjective_of_cotangentPullback_surjective_nilAug (q.app n) (hG n) fun w => ?_
  obtain ⟨v, rfl⟩ := G.omegaLevel_surjective n w
  obtain ⟨u, rfl⟩ := hq v
  exact ⟨u.1 n, rfl⟩

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaInductiveStep
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

open GlobalTheory.TwistTop

namespace GlobalTheory.ProjStep

theorem archInt_refines {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {N L : HermLB p} {ρ : N.B.ι → L.B.ι} (h : Refines N L ρ 0) {r : L.B.ι → X.functionFieldˣ}
    (hr : IsRatSec L.B r) (e : ℕ) :
    N.archInt N e (h.isRatSec hr) = L.archInt L e hr := by
  unfold HermLB.archInt
  rw [h.div hr]
  refine finsum_congr fun σ => ?_
  rw [h.chernInt]
  exact Weight.chernInt_congr (isOpen_offSupp _).measurableSet fun y hy => h.logNorm hr hy

end GlobalTheory.ProjStep

namespace GlobalTheory.ProjStep

theorem main : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ (y : Y) (e : ℕ), CharZero Γ(clo y, ⊤) → HasDim y (e + 1 + 1) → (∀ w : Y, HasDim w (e + 1) → h' w = (π.residueDegree w : ℝ) * h (π w)) → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' H H' y e hc hy hrec
  have hAX : IsAmb p := isAmb_of_isArithVar hX
  have hAY : IsAmb q := isAmb_of_isArithVar hY
  have := hX.isNoetherian
  have := hY.isNoetherian
  obtain ⟨hbdX, -, -, -, hsubX, hgenX⟩ := _root_.GlobalTheory.MixHt.hasDim_basic k X p hAX
  obtain ⟨-, -, -, -, hsubY, hgenY⟩ := _root_.GlobalTheory.MixHt.hasDim_basic k Y q hAY
  obtain ⟨g, hgc, hgη, hgdeg⟩ := _root_.GlobalTheory.MixHt.clo_restrict_dominant X Y π y

  have hdW : topologicalKrullDim (clo y) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    refine (hgenY (clo y) (e + 1 + 1)).1 ((hsubY (clo y) (cloι y) _ _).1 ?_)
    rw [cloι_genericPoint]; exact hy
  have hcZ : CharZero Γ(clo (π y), ⊤) := g.appTop.hom.charZero
  have hg1 : g ≫ cloι (π y) ≫ p = cloι y ≫ q := by
    rw [← Category.assoc, hgc, Category.assoc, hπ]
  have hC : (g ≫ cloι (π y)) ≫ p = cloι y ≫ q := by rw [Category.assoc]; exact hg1
  have hη' : g (genericPoint (clo y)) ⤳ genericPoint (clo (π y)) := hgη ▸ specializes_rfl
  have happ (w : clo y) : π (cloι y w) = cloι (π y) (g w) := by
    have := congrArg (fun f : clo y ⟶ X => f w) hgc
    simpa using this.symm
  have hδ : g.residueDegree (genericPoint (clo y)) = π.residueDegree y := by
    rw [hgdeg, cloι_genericPoint]

  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr (cloι (π y))).isLB
  have hr1 := MultPull.isRatSec_pull_map g hη' hr
  have ref1 : Refines (L.pull (g ≫ cloι (π y)) hC)
      ((L.restr (cloι (π y))).pull g hg1) (fun c _ => c) 0 := by
    refine { le := ?_, g := ?_, φ := ?_ }
    · intro c z hz
      exact Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hz a
    · intro W s z c c' hc hc'
      have h₁ : (s ≫ g) z ∈ (L.B.pull (cloι (π y))).U c := Set.mem_iInter.2 fun a => Set.mem_iInter.1 hc a
      have h₂ : (s ≫ g) z ∈ (L.B.pull (cloι (π y))).U c' := Set.mem_iInter.2 fun a => Set.mem_iInter.1 hc' a
      have h₃ : s z ∈ ((L.B.pull (cloι (π y))).pull g).U (fun _ => c) := Set.mem_iInter.2 fun _ => h₁
      have h₄ : s z ∈ ((L.B.pull (cloι (π y))).pull g).U (fun _ => c') := Set.mem_iInter.2 fun _ => h₂
      have e₁ := gm_pull_g (L.B.pull (cloι (π y))) g s z (fun _ => c) (fun _ => c') h₃ h₄
      have e₂ := gm_pull_g L.B (cloι (π y)) (s ≫ g) z c c' h₁ h₂
      have e₃ := gm_pull_g L.B (g ≫ cloι (π y)) s z c c' hc hc'
      rw [← Category.assoc] at e₃
      exact e₃.trans (e₁.trans e₂).symm
    · intro σ c z hz
      refine ((L.φ σ).pull_φ (g ≫ cloι (π y)) hC c z).trans (Eq.symm ((add_zero _).trans ?_))
      refine (((L.restr (cloι (π y))).φ σ).pull_φ g hg1 (fun _ => c) z).trans (((L.φ σ).pull_φ (cloι (π y)) rfl _ _).trans ?_)
      exact congrArg _ (Subtype.ext (Category.assoc _ _ _))
  have hrC := ref1.isRatSec hr1
  obtain ⟨ρ, ref2⟩ : ∃ ρ, Refines ((L.pull π hπ).restr (cloι y)) (L.pull (g ≫ cloι (π y)) hC) ρ 0 := by
    have key : ∀ (f : clo y ⟶ X) (hf : f ≫ p = cloι y ≫ q), f = cloι y ≫ π →
        ∃ ρ, Refines ((L.pull π hπ).restr (cloι y)) (L.pull f hf) ρ 0 := by
      rintro f hf rfl
      refine ⟨fun c => c PUnit.unit, { le := ?_, g := ?_, φ := ?_ }⟩
      · intro c z hz
        exact Set.mem_iInter.2 fun a => Set.mem_iInter.1 (Set.mem_iInter.1 hz PUnit.unit) a
      · intro W s z c c' hc hc'
        have h₁ := Set.mem_iInter.1 hc PUnit.unit
        have h₂ := Set.mem_iInter.1 hc' PUnit.unit
        refine (gm_pull_g _ (cloι y) s z c c' hc hc').trans ((gm_pull_g _ π (s ≫ cloι y) z _ _ h₁ h₂).trans ?_)
        refine Eq.trans ?_ (gm_pull_g _ (cloι y ≫ π) s z (c PUnit.unit) (c' PUnit.unit)
          (Set.mem_iInter.2 fun a => Set.mem_iInter.1 h₁ a) (Set.mem_iInter.2 fun a => Set.mem_iInter.1 h₂ a)).symm
        rw [Category.assoc]
      · intro σ c z hz
        refine (((L.pull π hπ).φ σ).pull_φ (cloι y) rfl c z).trans (((L.φ σ).pull_φ π hπ _ _).trans ?_)
        refine Eq.trans ?_ (((L.φ σ).pull_φ (cloι y ≫ π) hf (c PUnit.unit) z).symm.trans (add_zero _).symm)
        exact congrArg _ (Subtype.ext (Category.assoc _ _ _))
    exact key _ hC hgc
  have hrA := ref2.isRatSec hrC
  obtain ⟨-, hrecW⟩ := H'.recursion_one (cloι y) hc (by omega : 1 ≤ e + 1) hdW hrA
  rw [cloι_genericPoint] at hrecW
  have ediv : ((L.pull π hπ).restr (cloι y)).div hrA = (((L.restr (cloι (π y))).pull g hg1)).div hr1 :=
    (ref2.div hrC).trans (ref1.div hr1)
  have earch : ((L.pull π hπ).restr (cloι y)).archInt ((L.pull π hπ).restr (cloι y)) (e + 1) hrA =
      ((L.restr (cloι (π y))).pull g hg1).archInt ((L.restr (cloι (π y))).pull g hg1) (e + 1) hr1 :=
    (archInt_refines ref2 hrC (e + 1)).trans (archInt_refines ref1 hr1 (e + 1))
  have hsum : ∑ᶠ w, ((((L.pull π hπ).restr (cloι y)).div hrA).mult w : ℝ) * h' (cloι y w) =
      (π.residueDegree y : ℝ) * ∑ᶠ z, (((L.restr (cloι (π y))).div hr).mult z : ℝ) * h (cloι (π y) z) := by
    rw [ediv, ← hδ]
    refine Eq.trans (finsum_congr fun w => ?_) (_root_.GlobalTheory.PushDiv.finsum_mult_pull k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q)
      (hAX.sub _) (hAY.sub _) g hg1 hgη (L.restr (cloι (π y))).B (L.restr (cloι (π y))).isLB r hr
      (fun z => h (cloι (π y) z)))
    by_cases hm : ((((L.restr (cloι (π y))).pull g hg1)).div hr1).mult w = 0
    · have hm' : ((((L.restr (cloι (π y))).pull g hg1)).div hr1).mult w = 0 := hm
      rw [hm, Int.cast_zero, zero_mul]
      exact (mul_eq_zero_of_left (Int.cast_eq_zero.2 hm) _).symm
    · have hco := CartierDiv.coheight_eq_one_of_mult_ne_zero hm
      have hd1 := ((_root_.GlobalTheory.MixHt.dimOne k (clo y) (cloι y ≫ q) (hAY.sub _) (e + 1) hdW).1 w).1 hco
      have hd2 := (hsubY (clo y) (cloι y) w (e + 1)).2 hd1
      rw [hrec _ hd2, happ, hgdeg]
      rfl

  obtain ⟨m, hm⟩ := hbdX
  obtain ⟨d', -, hd'⟩ := hm (π y)
  obtain ⟨hle, hiff⟩ := _root_.GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff k X Y p q hAX hAY π hπ y (e + 1 + 1) d' hy hd'
  have hdZ : topologicalKrullDim (clo (π y)) = (d' : WithBot ℕ∞) := by
    refine (hgenX (clo (π y)) d').1 ((hsubX (clo (π y)) (cloι (π y)) _ _).1 ?_)
    rw [cloι_genericPoint]; exact hd'
  have hWv := hY.of_isClosedImmersion (cloι y) hc hdW
  rw [hsum, earch] at hrecW
  by_cases h0 : π.residueDegree y = 0
  ·
    have hlt : d' < e + 1 + 1 := lt_of_le_of_ne hle fun h1 => hiff.2 h1.symm h0
    have hd0 : d' ≠ 0 := fun h2 => hX.dim_ne_zero (cloι (π y)) hcZ (by rw [hdZ, h2]; rfl)
    obtain ⟨e0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
    have hZv0 := hX.of_isClosedImmersion (cloι (π y)) hcZ (e := e0) hdZ
    have hzero (σ : k →+* ℂ) (ε : ℤˣ) :
        (((L.restr (cloι (π y))).pull g hg1).φ σ).chernPart (e + 1) ε = 0 :=
      _root_.GlobalTheory.ChernLowDim.chernPart_pull_of_lt k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) e0 (e + 1) hZv0 hWv (by omega) g hg1 hgη
        (L.restr (cloι (π y))) σ ε
    have harch0 : ((L.restr (cloι (π y))).pull g hg1).archInt ((L.restr (cloι (π y))).pull g hg1) (e + 1) hr1 = 0 := by
      unfold HermLB.archInt Weight.chernInt
      simp [hzero]
    rw [harch0, h0] at hrecW
    rw [hrecW, h0]
    simp
  ·
    have hde : d' = e + 1 + 1 := (hiff.1 h0).symm
    subst hde
    have hZv := hX.of_isClosedImmersion (cloι (π y)) hcZ hdZ
    obtain ⟨-, hrecZ⟩ := H.recursion_one (cloι (π y)) hcZ (by omega : 1 ≤ e + 1) hdZ hr
    rw [cloι_genericPoint] at hrecZ
    have hpa := _root_.GlobalTheory.ArchPull.archInt_pull k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) (e + 1) hZv hWv g hg1 hgη
      (hδ ▸ h0) (L.restr (cloι (π y))) (L.restr (cloι (π y))) r hr
    rw [hδ] at hpa
    rw [hrecW, hpa, hrecZ]
    ring

end GlobalTheory.ProjStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaPointCurve
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.ProjCurve

section SlopeTestRemainingChoices

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}


open GlobalTheory.TwistTop in
theorem refines_trans {N L M : HermLB p} {π : N.B.ι → L.B.ι} {π' : L.B.ι → M.B.ι}
    (h : Refines N L π 0) (h' : Refines L M π' 0) : Refines N M (fun c => π' (π c)) 0 := by
  refine ⟨fun c => (h.le c).trans (h'.le _), ?_, ?_⟩
  · intro Z r z c c' hc hc'
    exact (h.g Z r z c c' hc hc').trans (h'.g Z r z _ _ (h.le _ hc) (h.le _ hc'))
  · intro σ c y hy
    rw [h.φ σ c y hy, h'.φ σ _ y (ptsIn_mono (h.le _) hy)]
    simp


open GlobalTheory.TwistTop in
theorem exists_refines_of_eq {N L L' : HermLB p} {π : N.B.ι → L.B.ι} (h : Refines N L π 0) (e : L = L') :
    ∃ π' : N.B.ι → L'.B.ι, Refines N L' π' 0 := by
  subst e
  exact ⟨π, h⟩

theorem pull_congr (L : HermLB p) {q : Y ⟶ Sp k} {f f' : Y ⟶ X} (e : f = f') (hf : f ≫ p = q)
    (hf' : f' ≫ p = q) : L.pull f hf = L.pull f' hf' := by
  subst e
  rfl

theorem isClosed_of_ne_generic {Z : Scheme.{0}} [IsIntegral Z] (hd : topologicalKrullDim Z = 1) {z : Z}
    (hz : z ≠ genericPoint Z) : IsClosed ({z} : Set Z) := by
  rcases Order.krullDim_le_one_iff.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 1 from hd.le)
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ with h | h
  · refine isClosed_of_closure_subset fun w hw => ?_
    have h₁ : (⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds Z) ≤
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
      closure_minimal (Set.singleton_subset_iff.2 hw) isClosed_closure
    have h₂ : z ∈ closure {w} := h h₁ (subset_closure rfl)
    exact ((specializes_iff_mem_closure.2 h₂).antisymm (specializes_iff_mem_closure.2 hw)).eq
  · exact absurd (IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@h
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _)))
      (genericPoint_spec Z)) hz

theorem log_card_residueField {W Z : Scheme.{0}} (g : W ⟶ Z) (w : W) [Finite (W.residueField w)] :
    Real.log (Nat.card (W.residueField w)) =
      (g.residueDegree w : ℝ) * Real.log (Nat.card (Z.residueField (g w))) := by
  letI := (g.residueFieldMap w).hom.toAlgebra
  have : Finite (Z.residueField (g w)) := Finite.of_injective _ (g.residueFieldMap w).hom.injective
  have : Module.Finite (Z.residueField (g w)) (W.residueField w) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := Z.residueField (g w)) (V := W.residueField w), Nat.cast_pow,
    Real.log_pow]
  rfl

end SlopeTestRemainingChoices


open GlobalTheory.TwistTop in
theorem main : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ),
    IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, CharZero Γ(clo y, ⊤) → HasDim y 1 →
    h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' H H' y hc hy
  have hAX := isAmb_of_isArithVar hX
  have hAY := isAmb_of_isArithVar hY
  have := hAX.isNoetherian
  have := hAY.isNoetherian
  obtain ⟨g, hgc, hgη, hgdeg⟩ := _root_.GlobalTheory.MixHt.clo_restrict_dominant X Y π y
  have D₁ := _root_.GlobalTheory.MixHt.hasDim_basic k Y q hAY
  have D₂ := _root_.GlobalTheory.MixHt.hasDim_basic k X p hAX

  have hdW : topologicalKrullDim (clo y) = 1 := by
    have h₁ := (D₁.2.2.2.2.1 (clo y) (cloι y) (genericPoint (clo y)) 1).1 (by rw [cloι_genericPoint]; exact hy)
    have h₂ := (D₁.2.2.2.2.2 (clo y) 1).1 h₁
    rw [h₂]
    rfl

  have hcZ : CharZero Γ(clo (π y), ⊤) := g.appTop.hom.charZero

  obtain ⟨m, hm⟩ := D₂.1
  obtain ⟨d', -, hd'⟩ := hm (π y)
  have hdZ' : topologicalKrullDim (clo (π y)) = d' :=
    (D₂.2.2.2.2.2 (clo (π y)) d').1 ((D₂.2.2.2.2.1 (clo (π y)) (cloι (π y)) _ d').1
      (by rw [cloι_genericPoint]; exact hd'))
  obtain ⟨hle, hiff⟩ := _root_.GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff k X Y p q hAX hAY π hπ y 1 d' hy hd'
  have hd1 : d' = 1 := by
    have h0 : d' ≠ 0 := by
      rintro rfl
      exact hX.dim_ne_zero (cloι (π y)) hcZ (hdZ'.trans (by rfl))
    omega
  subst hd1
  have hdZ : topologicalKrullDim (clo (π y)) = 1 := hdZ'.trans (by rfl)
  have hdeg : π.residueDegree y ≠ 0 := hiff.2 rfl
  have hdegη : g.residueDegree (genericPoint (clo y)) = π.residueDegree y := by
    rw [hgdeg, cloι_genericPoint]
  have hW : IsArithVar (cloι y ≫ q) 0 := hY.of_isClosedImmersion (cloι y) hc hdW
  have hZ : IsArithVar (cloι (π y) ≫ p) 0 := hX.of_isClosedImmersion (cloι (π y)) hcZ hdZ

  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr (cloι (π y))).isLB
  have hg' : g ≫ cloι (π y) ≫ p = cloι y ≫ q := by
    rw [← Category.assoc, hgc, Category.assoc, hπ]
  have hr' := MultPull.isRatSec_pull_map g (hgη ▸ specializes_rfl : g (genericPoint (clo y)) ⤳ genericPoint _) hr

  have h₁ : (cloι y ≫ π) ≫ p = cloι y ≫ q := by rw [Category.assoc, hπ]
  have h₂ : (g ≫ cloι (π y)) ≫ p = cloι y ≫ q := by rw [hgc, h₁]
  obtain ⟨ρ, hρ⟩ := exists_refines_of_eq (L.refines_pull_pull π hπ (cloι y) rfl h₁)
    (pull_congr L hgc.symm h₁ h₂)
  have hρ' := refines_trans hρ (L.refines_pull_comp (cloι (π y)) rfl g hg' h₂)

  have e₁ := H'.point (clo y) (cloι y) hc hdW _ (hρ'.isRatSec hr')
  rw [cloι_genericPoint] at e₁
  have e₂ : ((L.pull π hπ).restr (cloι y)).curveDeg (hρ'.isRatSec hr') =
      ((L.restr (cloι (π y))).pull g hg').curveDeg hr' := by
    unfold HermLB.curveDeg
    rw [hρ'.div hr']
    refine congrArg _ (finsum_congr fun σ => finsum_congr fun z => hρ'.logNorm hr' (mem_offSupp.2 ?_))
    rw [under_eq_genericPoint hW z]
    exact CartierDiv.genericPoint_notMem_supp _

  have e₃ := H.point (clo (π y)) (cloι (π y)) hcZ hdZ r hr
  rw [cloι_genericPoint] at e₃

  have a₁ := GlobalTheory.ArchDimZero.main k (clo y) (cloι y ≫ q) hW ((L.restr (cloι (π y))).pull g hg')
    ((L.restr (cloι (π y))).pull g hg') _ hr'
  have a₂ := _root_.GlobalTheory.ArchPull.archInt_pull k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) 0 hZ hW g hg' hgη
    (hdegη ▸ hdeg) (L.restr (cloι (π y))) (L.restr (cloι (π y))) r hr
  have a₃ := GlobalTheory.ArchDimZero.main k (clo (π y)) (cloι (π y) ≫ p) hZ (L.restr (cloι (π y)))
    (L.restr (cloι (π y))) r hr

  have f₁ := _root_.GlobalTheory.PushDiv.finsum_mult_pull k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) (hAX.sub _) (hAY.sub _) g hg' hgη
    (L.restr (cloι (π y))).B (L.restr (cloι (π y))).isLB r hr (fun z => Real.log (Nat.card ((clo (π y)).residueField z)))
  have f₂ : ∑ᶠ w, ((((L.restr (cloι (π y))).pull g hg').div hr').mult w : ℝ) *
      Real.log (Nat.card ((clo y).residueField w)) =
      ∑ᶠ w, ((((L.restr (cloι (π y))).pull g hg').div hr').mult w : ℝ) *
      ((g.residueDegree w : ℝ) * Real.log (Nat.card ((clo (π y)).residueField (g w)))) := by
    refine finsum_congr fun w => ?_
    by_cases hw : (((L.restr (cloι (π y))).pull g hg').div hr').mult w = 0
    · rw [hw, Int.cast_zero, zero_mul, zero_mul]
    have hne : w ≠ genericPoint (clo y) := fun e =>
      CartierDiv.genericPoint_notMem_supp _ (e ▸ CartierDiv.mem_supp_of_mult_ne_zero hw)
    have := hW.finite_residueField (isClosed_of_ne_generic hdW hne)
    rw [log_card_residueField g w]
  rw [e₁, e₂, e₃]
  unfold HermLB.curveDeg
  rw [← a₁, ← a₃, f₂]
  rw [hdegη] at f₁ a₂
  rw [a₂]
  erw [f₁]
  ring

end GlobalTheory.ProjCurve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBundleBirigidSymmetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem canon_isBiRig : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → IsBiRig G P := by
  intro R _ _ _ hCN Q G _ _ P hC
  obtain ⟨hP, D', F, A', G', i1, i2, U', oA, oG, inc, pr, hsemi, hlin, hinc, hpr, hip, hpi, hiso⟩ := hC
  have hL : U'.LG.L.IsLB := U'.LG.isLB
  have hros := _root_.GlobalTheory.Mum.OLinRosati.main R hCN D' F.O F.o A' G' U' oA oG hsemi hlin
  have hie : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have hf : IsMonHom (inc ≫ oG.act F.f) := by have := oG.hom F.f; infer_instance
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.MumAxes.gen_axes (Sp R) G G' U'.LG.L hL inc (inc ≫ oG.act F.f) hinc hf P hP hiso
  exact ⟨hP, h1, h2, _root_.GlobalTheory.MumSymPull.lbIso_swap (Sp R) G G' U'.LG.L hL F.O oG hros F.e F.f inc hinc hie F.alg.2.1 P hP hiso⟩

end GlobalTheory.Mum
end

