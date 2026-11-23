module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0462
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfIsIntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnWirtWordMulExpComp
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

noncomputable section

namespace GlobalTheory.WirtChain

open Complex

variable {Φ I : Type} [Fintype Φ] [Fintype I]

theorem contDiffOn_wirt' {V : Set (Φ → ℂ)} (hV : IsOpen V) {g : (Φ → ℂ) → ℂ} (hg : ContDiffOn ℝ ∞ g V)
    (τ : Φ) (bar : Bool) : ContDiffOn ℝ ∞ (wirt τ bar g) V := by
  have hd := ((contDiffOn_infty_iff_fderiv_of_isOpen hV).1 hg).2
  unfold wirt
  exact ((hd.clm_apply contDiffOn_const).add (contDiffOn_const.mul (hd.clm_apply contDiffOn_const))).div_const 2

theorem contDiffOn_wirtWord' {V : Set (Φ → ℂ)} (hV : IsOpen V) {g : (Φ → ℂ) → ℂ} (hg : ContDiffOn ℝ ∞ g V)
    (w : List (Φ × Bool)) : ContDiffOn ℝ ∞ (wirtWord w g) V := by
  induction w with
  | nil => simpa [wirtWord_nil] using hg
  | cons a w ih => rw [wirtWord_cons]; exact contDiffOn_wirt' hV ih _ _

open Classical in
theorem fderiv_eq_sum_wirt' (h : (Φ → ℂ) → ℂ) (y u : Φ → ℂ) :
    fderiv ℝ h y u = ∑ τ, (u τ * wirt τ false h y + (starRingEnd ℂ) (u τ) * wirt τ true h y) := by
  have hu : u = ∑ τ, ((u τ).re • (Pi.single τ (1:ℂ) : Φ → ℂ) + (u τ).im • (Pi.single τ I : Φ → ℂ)) := by
    ext τ'
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp [Complex.re_add_im]
  conv_lhs => rw [hu]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_add (f := _), map_smul, map_smul]
  simp only [wirt, Bool.false_eq_true, if_false, if_true, real_smul]
  set A := fderiv ℝ h y (Pi.single τ 1)
  set B := fderiv ℝ h y (Pi.single τ I)
  have hc : (starRingEnd ℂ) (u τ) = (u τ).re - (u τ).im * I := by
    apply Complex.ext <;> simp
  have hu' : u τ = (u τ).re + (u τ).im * I := (Complex.re_add_im _).symm
  have key : ∀ (a c : ℝ) (A B : ℂ), (a:ℂ) * A + (c:ℂ) * B =
      ((a:ℂ) + (c:ℂ) * I) * ((A + -I * B) / 2) + ((a:ℂ) - (c:ℂ) * I) * ((A + I * B) / 2) := by
    intro a c A B
    ring_nf
    rw [I_sq]
    ring
  have := key (u τ).re (u τ).im A B
  rw [← hu', ← hc] at this
  linear_combination this

section Rep

variable (U : Set (I → ℂ)) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (l : (I → ℂ) → ℂ)

inductive ExpSum : (ℂ → (I → ℂ) → ℂ) → Prop
  | zero : ExpSum fun _ _ => 0
  | term (n : ℕ) (β : (I → ℂ) → ℂ) (w : List (Φ × Bool)) : ContDiffOn ℝ ∞ β U →
      ExpSum fun σ z => σ ^ n * β z * Complex.exp (-σ * l z) * wirtWord w (G σ) (t z)
  | add {F₁ F₂ : ℂ → (I → ℂ) → ℂ} : ExpSum F₁ → ExpSum F₂ → ExpSum fun σ z => F₁ σ z + F₂ σ z

variable {U G t l}

theorem ExpSum.const_mul {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) (c : ℂ) :
    ExpSum U G t l fun σ z => c * F σ z := by
  induction hF with
  | zero => simpa using ExpSum.zero (U := U) (G := G) (t := t) (l := l)
  | term n β w hβ =>
    have h := ExpSum.term (U := U) (G := G) (t := t) (l := l) n (fun z => c * β z) w (contDiffOn_const.mul hβ)
    convert h using 2
    ring_nf
  | add _ _ h₁ h₂ =>
    have h := ExpSum.add h₁ h₂
    convert h using 2
    ring_nf

theorem ExpSum.sum {α : Type} (s : Finset α) (F : α → ℂ → (I → ℂ) → ℂ) (hF : ∀ a ∈ s, ExpSum U G t l (F a)) :
    ExpSum U G t l fun σ z => ∑ a ∈ s, F a σ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ExpSum.zero (U := U) (G := G) (t := t) (l := l)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ExpSum.add (hF a (Finset.mem_insert_self a s)) (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

theorem ExpSum.holo {D : Set ℂ} {V : Set (Φ → ℂ)} (hmaps : Set.MapsTo t U V)
    (hGh : ∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) {z : I → ℂ} (hz : z ∈ U) :
    DifferentiableOn ℂ (fun σ => F σ z) D := by
  induction hF with
  | zero => exact differentiableOn_const _
  | term n β w hβ =>
    exact (((differentiableOn_id.pow n).mul (differentiableOn_const _)).mul
      ((differentiableOn_id.neg.mul_const (l z)).cexp)).mul (hGh w (t z) (hmaps hz))
  | add _ _ h₁ h₂ => exact h₁.add h₂

theorem ExpSum.smooth {D : Set ℂ} {V : Set (Φ → ℂ)} (hV : IsOpen V) (hmaps : Set.MapsTo t U V)
    (ht : ContDiffOn ℝ ∞ t U) (hl : ContDiffOn ℝ ∞ l U)
    (hGs : ∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) {σ : ℂ} (hσ : σ ∈ D) :
    ContDiffOn ℝ ∞ (F σ) U := by
  induction hF with
  | zero => exact contDiffOn_const
  | term n β w hβ =>
    exact ((contDiffOn_const.mul hβ).mul (contDiffOn_const.mul hl).cexp).mul
      ((contDiffOn_wirtWord' hV (hGs σ hσ) w).comp ht hmaps)
  | add _ _ h₁ h₂ => exact h₁.add h₂

end Rep

section Deriv

variable {U : Set (I → ℂ)} {G : ℂ → (Φ → ℂ) → ℂ} {t : (I → ℂ) → Φ → ℂ} {l : (I → ℂ) → ℂ}

theorem ExpSum.deriv {D : Set ℂ} {V : Set (Φ → ℂ)} (hU : IsOpen U) (hV : IsOpen V) (hmaps : Set.MapsTo t U V)
    (ht : ContDiffOn ℝ ∞ t U) (hl : ContDiffOn ℝ ∞ l U)
    (hGs : ∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) (v : I → ℂ) :
    ∃ F', ExpSum U G t l F' ∧ ∀ σ ∈ D, ∀ z ∈ U, fderiv ℝ (F σ) z v = F' σ z := by
  have hdt := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 ht).2
  have hdl := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hl).2
  have hdtv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ t z v) U := hdt.clm_apply contDiffOn_const
  have hdlv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ l z v) U := hdl.clm_apply contDiffOn_const
  induction hF with
  | zero => exact ⟨fun _ _ => 0, ExpSum.zero, fun σ _ z _ => by simp⟩
  | @add F₁ F₂ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨F₁', h₁', e₁⟩ := ih₁
    obtain ⟨F₂', h₂', e₂⟩ := ih₂
    refine ⟨fun σ z => F₁' σ z + F₂' σ z, ExpSum.add h₁' h₂', fun σ hσ z hz => ?_⟩
    have d₁ := ((h₁.smooth hV hmaps ht hl hGs hσ).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
    have d₂ := ((h₂.smooth hV hmaps ht hl hGs hσ).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
    show fderiv ℝ (fun y => F₁ σ y + F₂ σ y) z v = F₁' σ z + F₂' σ z
    have hsum : HasFDerivAt (fun y => F₁ σ y + F₂ σ y) _ z := d₁.hasFDerivAt.add d₂.hasFDerivAt
    rw [hsum.fderiv, ContinuousLinearMap.add_apply, e₁ σ hσ z hz, e₂ σ hσ z hz]
  | term n β w hβ =>
    have hdb := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hβ).2
    have hdbv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ β z v) U := hdb.clm_apply contDiffOn_const
    refine ⟨fun σ z => (σ ^ n * fderiv ℝ β z v * Complex.exp (-σ * l z) * wirtWord w (G σ) (t z) +
        σ ^ (n + 1) * (-(β z * fderiv ℝ l z v)) * Complex.exp (-σ * l z) * wirtWord w (G σ) (t z)) +
        ∑ τ : Φ, (σ ^ n * (β z * fderiv ℝ t z v τ) * Complex.exp (-σ * l z) * wirtWord ((τ, false) :: w) (G σ) (t z) +
          σ ^ n * (β z * (starRingEnd ℂ) (fderiv ℝ t z v τ)) * Complex.exp (-σ * l z) *
            wirtWord ((τ, true) :: w) (G σ) (t z)), ?_, ?_⟩
    · refine ExpSum.add (ExpSum.add (ExpSum.term n _ w hdbv) (ExpSum.term (n + 1) _ w (hβ.mul hdlv).neg))
        (ExpSum.sum Finset.univ _ fun τ _ => ExpSum.add (ExpSum.term n _ _ (hβ.mul (contDiffOn_pi.1 hdtv τ)))
          (ExpSum.term n _ _ (hβ.mul ?_)))
      have := Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.1 hdtv τ)
      simpa [Function.comp_def] using this
    · intro σ hσ z hz
      have hzn := hU.mem_nhds hz
      set W := wirtWord w (G σ) with hWdef
      have hWs : ContDiffOn ℝ ∞ W V := contDiffOn_wirtWord' hV (hGs σ hσ) w
      have hb' : HasFDerivAt β (fderiv ℝ β z) z :=
        ((hβ.differentiableOn (by simp)).differentiableAt hzn).hasFDerivAt
      have hl' : HasFDerivAt l (fderiv ℝ l z) z :=
        ((hl.differentiableOn (by simp)).differentiableAt hzn).hasFDerivAt
      have ht' : HasFDerivAt t (fderiv ℝ t z) z :=
        ((ht.differentiableOn (by simp)).differentiableAt hzn).hasFDerivAt
      have hW' : HasFDerivAt W (fderiv ℝ W (t z)) (t z) :=
        ((hWs.differentiableOn (by simp)).differentiableAt (hV.mem_nhds (hmaps hz))).hasFDerivAt
      have hE := (hl'.const_mul (-σ)).cexp
      have hWt := hW'.comp z ht'
      have hall := ((hb'.const_mul (σ ^ n)).mul hE).mul hWt
      have hall' : HasFDerivAt (fun y => σ ^ n * β y * Complex.exp (-σ * l y) * W (t y)) _ z := hall
      rw [hall'.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.comp_apply, Function.comp_apply, Pi.mul_apply]
      rw [fderiv_eq_sum_wirt' W (t z) (fderiv ℝ t z v)]
      simp only [wirtWord_cons]
      rw [← hWdef]
      have hs : ∀ τ : Φ, σ ^ n * β z * Complex.exp (-σ * l z) * (fderiv ℝ t z v τ * wirt τ false W (t z) +
          (starRingEnd ℂ) (fderiv ℝ t z v τ) * wirt τ true W (t z)) =
          σ ^ n * (β z * fderiv ℝ t z v τ) * Complex.exp (-σ * l z) * wirt τ false W (t z) +
          σ ^ n * (β z * (starRingEnd ℂ) (fderiv ℝ t z v τ)) * Complex.exp (-σ * l z) * wirt τ true W (t z) :=
        fun τ => by ring
      rw [Finset.mul_sum]
      simp only [hs]
      ring

end Deriv


open Classical in
theorem differentiableOn_wirtWord_mul_exp_comp : ∀ (Φ I : Type) [Fintype Φ] [Fintype I] (U : Set (I → ℂ)) (V : Set (Φ → ℂ)) (D : Set ℂ) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (b l : (I → ℂ) → ℂ), IsOpen U → IsOpen V → Set.MapsTo t U V → ContDiffOn ℝ ∞ t U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ l U → (∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V) → (∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D) → ∀ w : List (I × Bool), ∀ z ∈ U, DifferentiableOn ℂ (fun σ => wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z')) z) D := by
  intro Φ I _ _ U V D G t b l hU hV hmaps ht hb hl hGs hGh w z hz
  have key : ∀ w : List (I × Bool), ∃ F, ExpSum U G t l F ∧ ∀ σ ∈ D,
      Set.EqOn (wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z'))) (F σ) U := by
    intro w
    induction w with
    | nil =>
      refine ⟨_, ExpSum.term 0 b [] hb, fun σ _ z _ => ?_⟩
      simp [wirtWord_nil]
    | cons a w ih =>
      obtain ⟨F, hF, hEq⟩ := ih
      obtain ⟨F₁, hF₁, hd₁⟩ := hF.deriv hU hV hmaps ht hl hGs (Pi.single a.1 1)
      obtain ⟨F₂, hF₂, hd₂⟩ := hF.deriv hU hV hmaps ht hl hGs (Pi.single a.1 Complex.I)
      refine ⟨fun σ z => (1 / 2 : ℂ) * (F₁ σ z + (if a.2 then Complex.I else -Complex.I) * F₂ σ z),
        (ExpSum.add hF₁ (hF₂.const_mul _)).const_mul _, fun σ hσ z hz => ?_⟩
      have hev : wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z')) =ᶠ[nhds z] F σ :=
        Filter.eventually_of_mem (hU.mem_nhds hz) fun y hy => hEq σ hσ hy
      rw [wirtWord_cons]
      simp only [wirt]
      rw [hev.fderiv_eq, hd₁ σ hσ z hz, hd₂ σ hσ z hz]
      ring
  obtain ⟨F, hF, hEq⟩ := key w
  exact (hF.holo hmaps hGh hz).congr fun σ hσ => hEq σ hσ hz

end GlobalTheory.WirtChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackQuotientEq
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilRigidity

theorem exists_preimage_quotient {R : Type} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R) (t : Sp R) :
    ∃ t₀ : Sp (R ⧸ I), spMap (Ideal.Quotient.mk I) t₀ = t := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hmem : t ∈ PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk I) : Set R) := by
    rw [Ideal.mk_ker]
    intro x hx
    exact (@nilradical_le_prime _ _ t.asIdeal t.isPrime) (hI hx)
  rw [← range_comap_of_surjective _ _ hsurj] at hmem
  obtain ⟨t₀, ht₀⟩ := hmem
  exact ⟨t₀, ht₀⟩

theorem eq_of_eq_on_quotient {R : Type} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R)
    (B B' : Over (Sp R)) [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B) (f g : B ⟶ B')
    (hfg : pullback.fst B.hom (spMap (Ideal.Quotient.mk I)) ≫ f.left =
      pullback.fst B.hom (spMap (Ideal.Quotient.mk I)) ≫ g.left)
    (hη : η[B] ≫ f = η[B] ≫ g) : f = g := by
  haveI := hB.proper
  let π := spMap (Ideal.Quotient.mk I)
  let c : B ⟶ B' := f * g⁻¹
  let j := pullback.fst B.hom π
  let j' : Over.mk (j ≫ B.hom) ⟶ B := Over.homMk j rfl
  have h1 : j' ≫ f = j' ≫ g := Over.OverMorphism.ext hfg
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[B] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  have hpt : ∀ x : B.left, c.left x = (η[B'] : 𝟙_ (Over (Sp R)) ⟶ B').left (B.hom x) := by
    intro x
    obtain ⟨t₀, ht₀⟩ := exists_preimage_quotient I hI (B.hom x)
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback B.hom π) x t₀ ht₀.symm
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    rfl
  have hη' : (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left ≫ B.hom = 𝟙 _ := Over.w η[B]
  have key : c.left = B.hom ≫ (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left ≫ c.left := by
    refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
    obtain ⟨V, hV, hV'⟩ := GlobalTheory.local_rigidity B.left (Sp R) B'.left B.hom _ c.left hη' inferInstance
      (GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.globalFns_holds B hB) (B.hom x)
      ((η[B'] : 𝟙_ (Over (Sp R)) ⟶ B').left (B.hom x)) (fun x' hx' ↦ by rw [hpt, hx'])
    exact ⟨B.hom ⁻¹ᵁ V, hV, hV'⟩
  have key' : c = toUnit B ≫ η[B] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

theorem eq_of_pullback_quotient_eq {R : Type} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    (B B' : Over (Sp R)) [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B) (f g : B ⟶ B') [IsMonHom f] [IsMonHom g]
    (h : (Over.pullback (spMap (Ideal.Quotient.mk I))).map f = (Over.pullback (spMap (Ideal.Quotient.mk I))).map g) :
    f = g := by
  have hI' : I ≤ nilradical R := by
    obtain ⟨n, hn⟩ := hI
    intro x hx
    exact ⟨n, by
      have : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at this
      simpa using this⟩
  refine eq_of_eq_on_quotient I hI' B B' hB f g ?_ (by rw [IsMonHom.one_hom, IsMonHom.one_hom])
  have e := congrArg (fun k ↦ k.left ≫ pullback.fst B'.hom (spMap (Ideal.Quotient.mk I))) h
  simp only [Over.pullback_map_left, pullback.lift_fst] at e
  exact e

end GlobalTheory.NilRigidity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalencePullbackIntegralAffineStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyEquivalence_pullback_integral_affine : ∀ (R : Type) [CommRing R] (F : Shv R) (A C : Type) [CommRing A] [CommRing C] [Algebra A C],
    (∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      Eqv R (spMap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom) F) →
    ∀ (Z Z' : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of A)) (h' : Z' ⟶ Spec (CommRingCat.of C)) (φ : Z' ⟶ Z),
    IsIntegralHom h → IsPullback φ h' h (Spec.map (CommRingCat.ofHom (algebraMap A C))) → Eqv R (sch.map φ) F := by
  first | (exact @GlobalTheory.EtC.eqv_pullback_integral_affine) | (exact GlobalTheory.EtC.eqv_pullback_integral_affine) | (intros; apply GlobalTheory.EtC.eqv_pullback_integral_affine  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etale_cohomology_vanishing_negative_degree_zero : A9 := by
  intro R _ F
  refine ⟨?_, ?_⟩
  · intro E n hn
    have hz : ∀ α : Cochain ((chains R).obj E) (res R F) n, α = 0 := by
      intro α
      apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 α 0
      intro p s h U x
      have hs : s < 0 := by omega
      haveI := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.2 s hs)
      exact Subsingleton.elim _ _
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := a.mk_surjective
    obtain ⟨b, rfl⟩ := b.mk_surjective
    have : a = b := Cocycle.ext (by rw [hz a.1, hz b.1])
    rw [this]
  · let f : ∀ X : Scheme.{0}, Sec F X →+ H R (sch.obj X) F 0 := fun X =>
      AddMonoidHom.mk' (secClass F (X := X)) (GlobalTheory.T.degreeZeroSectionClass_properties R F X).2.2.1
    refine ⟨fun X => AddEquiv.ofBijective (f X) (GlobalTheory.T.degreeZeroSectionClass_properties R F X).2.1, ?_, ?_⟩
    · intro Y X g s
      exact (GlobalTheory.T.degreeZeroSectionClass_properties R F X).2.2.2.1 g s
    · intro X s
      obtain ⟨α, hα⟩ := (secClass F s).mk_surjective
      exact ⟨α, hα, ((GlobalTheory.T.degreeZeroSectionClass_properties R F X).1 s α).2 hα⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleHeightOneOfRegularLocalRing
section
open IsLocalRing

namespace GlobalTheory.BranchPurity

theorem dim_lt (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ maximalIdeal R) : ringKrullDim (Localization.AtPrime p) < ringKrullDim R := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, ← maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_lt_coe.mpr (Ideal.height_strict_mono_of_isPrime_of_isPrime
    (lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hp))

theorem regular_localization (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) (p : Ideal R) [p.IsPrime] :
    ((maximalIdeal (Localization.AtPrime p)).spanFinrank : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime p) := by
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hR
  haveI : IsRegularRing R := GlobalTheory.isRegularRing_of_isRegularLocalRing R
  exact (IsRegularRing.isRegularLocalRing_localization p).spanFinrank_maximalIdeal

theorem integrallyClosed (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) : IsIntegrallyClosed R := by
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hR
  exact (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2

theorem not_isField_localization (R : Type) [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ ⊥) : ¬ IsField (Localization.AtPrime p) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
  intro h
  apply hp
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime p)) :=
    IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  exact (Ideal.map_eq_bot_iff_of_injective hinj).mp h

theorem finiteRing_sq_sub_mul_sq_eq_of_card : ∀ (n : ℕ) (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (maximalIdeal R).spanFinrank = n → (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro R A _ _ _ _ _ _ _ _ _ _ hn hR hF hA
  haveI : IsIntegrallyClosed R := integrallyClosed R hR
  have hfree : Module.Free R A := by
    by_cases h2 : ringKrullDim R ≤ 2
    · exact GlobalTheory.PurFree.free_of_isIntegrallyClosed R A hR h2
    · refine _root_.GlobalTheory.PurityStep.free_of_etale_punctured R A hR ?_ ?_
      · rw [not_le] at h2
        have h2' : ((2 : ℕ) : WithBot ℕ∞) < ringKrullDim R := by exact_mod_cast h2
        rw [← hR] at h2' ⊢
        have : 2 < (maximalIdeal R).spanFinrank := by exact_mod_cast h2'
        exact_mod_cast this
      · intro p _ hp
        by_cases hb : p = ⊥
        · subst hb
          exact GlobalTheory.etale_fractionField_of_etale_height_one R A hF hA
        obtain ⟨hdom, hic, hfs⟩ := GlobalTheory.atPrime_tensor_isDomain_isIntegrallyClosed_faithfulSMul R A p
        have hlt := dim_lt R p hp
        have hreg := regular_localization R hR p
        refine IH (maximalIdeal (Localization.AtPrime p)).spanFinrank ?_ (Localization.AtPrime p)
          (TensorProduct R (Localization.AtPrime p) A) rfl hreg (not_isField_localization R p hb)
          (GlobalTheory.etale_localization_atPrime_of_height_one R A p hA)
        rw [← hreg, ← hR, hn] at hlt
        exact_mod_cast hlt
  exact GlobalTheory.PurityDisc.etale_of_etale_height_one R A hF hA

theorem etale_of_etale_height_one : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 1 ≤ ringKrullDim R → ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  intro R A _ _ _ _ _ _ _ _ _ _ hR _ hF hA
  exact finiteRing_sq_sub_mul_sq_eq_of_card _ R A rfl hR hF hA

end GlobalTheory.BranchPurity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndLatticeTraceOne
section
noncomputable section

namespace GlobalTheory.LieDisc

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def rankOne (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b => x a * ∑ k, G b k * cc (y k)

theorem rankOne_mulVec (G : Matrix (Fin r) (Fin r) E) (x y v : Fin r → E) :
    rankOne G x y *ᵥ v = herm G v y • x := by
  ext a
  simp only [rankOne, mulVec, dotProduct, of_apply, herm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem trace_rankOne (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    (rankOne G x y).trace = herm G x y := by
  simp only [Matrix.trace, diag, rankOne, of_apply, herm, Finset.mul_sum, mul_assoc]

def traceIdeal (Λ : Submodule (𝓞 E) (Fin r → E)) : Ideal (𝓞 E) where
  carrier := {s | ∃ Z ∈ endLat Λ, Z.trace = (s : E)}
  zero_mem' := ⟨0, (endLat Λ).zero_mem, by simp⟩
  add_mem' {s t} hs ht := by
    obtain ⟨Z, hZ, e⟩ := hs
    obtain ⟨Z', hZ', e'⟩ := ht
    exact ⟨Z + Z', (endLat Λ).add_mem hZ hZ', by rw [trace_add, e, e']; push_cast; rfl⟩
  smul_mem' c {s} hs := by
    obtain ⟨Z, hZ, e⟩ := hs
    refine ⟨(c : E) • Z, smul_mem_endLat c.isIntegral_coe hZ, ?_⟩
    rw [trace_smul, e, smul_eq_mul, smul_eq_mul]
    push_cast; rfl

theorem exists_endLat_trace_eq_one (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hr : 1 ≤ r)
    (h : SelfDualLat G Λ) : ∃ Z ∈ endLat Λ, Z.trace = 1 := by
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm G x y) := fun x hx => (h.2.2.2.2 x).2 hx
  have htop : traceIdeal Λ = ⊤ := by
    by_contra hT
    refine GlobalTheory.UCls.Det.exists_herm_notMem hr h (traceIdeal Λ) hT fun x hx y hy =>
      ⟨⟨herm G x y, hint x hx y hy⟩, ⟨rankOne G x y, fun v hv => ?_, trace_rankOne G x y⟩, rfl⟩
    rw [rankOne_mulVec]
    exact smul_mem_of_isIntegral (hint v hv y hy) hx
  have h1 : (1 : 𝓞 E) ∈ traceIdeal Λ := htop ▸ Submodule.mem_top
  obtain ⟨Z, hZ, e⟩ := h1
  exact ⟨Z, hZ, by rw [e]; simp⟩

end GlobalTheory.LieDisc
end
end

