module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEndOfEighthPowerOfPolAVPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem isDiagEnd_pullback : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}}
    (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (ψ : P'.A.left ⟶ P.A.left)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P u ε → IsGrpPullback P'.A P.A f ψ →
    LBIso P'.L (P.L.pull ψ) → ∃ ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A),
      IsDiagEnd F W P' (f ≫ u) ε' ∧ ∀ E, (ε' E).left ≫ ψ = ψ ≫ (ε E).left := by
  intro g n F W T T' P P' u f φ ε hS hφ hL
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hdiag⟩ := hS
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n _ (zetaAway n) T T' (u ≫ F.s) ((f ≫ u) ≫ F.s) f c
    (by rw [Category.assoc])
  have hc'u : SiegPB c' F.univ (f ≫ u) := GlobalTheory.SiegelPullComp.pb_comp hc hc'
  obtain ⟨ψ, ψ₂, hψ, hsq, hw, -⟩ := hc'
  have hp := hψ.1
  have hφp := hφ.1
  have wa : ∀ a, (φ ≫ (pr a).left) ≫ c.A.hom = P'.A.hom ≫ f := fun a => by
    rw [Category.assoc, Over.w, hφp.w]
  let pr' : Fin 8 → (P'.A ⟶ c'.A) := fun a =>
    Over.homMk (hp.lift (φ ≫ (pr a).left) P'.A.hom (wa a)) (hp.lift_snd _ _ _)
  have hpr'ψ : ∀ a, (pr' a).left ≫ ψ = φ ≫ (pr a).left := fun a => hp.lift_fst _ _ _
  have push_comp : ∀ {T₁ : Over T'} (x : T₁ ⟶ P'.A) a, pushPt hψ.1.w (x ≫ pr' a) = pushPt hφ.1.w x ≫ pr a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ (pr' a).left) ≫ ψ = (x.left ≫ φ) ≫ (pr a).left
      rw [Category.assoc, hpr'ψ, Category.assoc])
  have pmψ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ c'.A), pushPt hψ.1.w (x * y) = pushPt hψ.1.w x * pushPt hψ.1.w y :=
    fun x y => map_mul (pushHom hψ _) x y
  have pmφ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have injψ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ c'.A}, pushPt hψ.1.w x = pushPt hψ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hψ _ e
  have injφ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hφ _ e
  have hmon : ∀ a, IsMonHom (pr' a) := fun a => by
    haveI := hpr a
    refine isMonHom_of_mul _ fun T₁ x y => injψ ?_
    rw [push_comp, pmψ, push_comp, push_comp, pmφ]
    exact MonObj.mul_comp _ _ _
  have huniv' : ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a := by
    intro T₁ y
    obtain ⟨x₀, hx₀, hu₀⟩ := huniv (Over.mk (T₁.hom ≫ f)) (fun a => pushPt hψ.1.w (y a))
    let x : T₁ ⟶ P'.A := Over.homMk (hφp.lift x₀.left T₁.hom (Over.w x₀)) (hφp.lift_snd _ _ _)
    have hx : pushPt hφ.1.w x = x₀ := Over.OverMorphism.ext (hφp.lift_fst _ _ _)
    have key : ∀ z : T₁ ⟶ P'.A, (∀ a, z ≫ pr' a = y a) ↔ ∀ a, pushPt hφ.1.w z ≫ pr a = pushPt hψ.1.w (y a) :=
      fun z => forall_congr' fun a => ⟨fun h => by rw [← push_comp, h], fun h => injψ (by rw [push_comp, h])⟩
    refine ⟨x, (key x).2 (by rw [hx]; exact hx₀), fun z hz => injφ ?_⟩
    exact (hu₀ _ ((key z).1 hz)).trans hx.symm
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr' ab.1) (pr' ab.2)).left ≫ ψ₂ = φ ≫ (lift (pr ab.1) (pr ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (φ ≫ P.A.hom)) (T' := P'.A)
      (𝟙 P'.A.left) (pr' ab.1) (pr' ab.2) (Z := P.A) φ (pr ab.1) (pr ab.2)
      ((Category.id_comp _).trans (hpr'ψ ab.1)) ((Category.id_comp _).trans (hpr'ψ ab.2)))
  have hbun' : LBIso P'.L (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left)
      (fun ab => W ab.1 ab.2)) := by
    let ε : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
    let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
    let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
    have l0 : (LB.LinComb c.P q ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε
    have l1 : (LB.LinComb c.P (fun ab => φ ≫ q ab) ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB _ ε
    have l2 : (LB.LinComb (c.P.pull ψ₂) q' ε).IsLB :=
      ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c.P.pull ψ₂) (pull_isLB c.isLB ψ₂) q' ε
    have l3 : (LB.LinComb c'.P q' ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε
    have refl1 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
      ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
    have i2 : LBIso (P.L.pull φ) ((LB.LinComb c.P q ε).pull φ) := GlobalTheory.SiegelPullComp.iso_pull φ hbun
    have i3 : LBIso ((LB.LinComb c.P q ε).pull φ) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
      LBIso.chartPull (chartPullOut c.P q ε φ _ fun _ => rfl) (chartPullId _) refl1
    have i4 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb (c.P.pull ψ₂) q' ε) :=
      LBIso.chartPull (chartPullId _)
        (chartPullLinComb c.P ψ₂ q' (fun ab => φ ≫ q ab) ε (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
    have i5 : LBIso (LB.LinComb (c.P.pull ψ₂) q' ε) (LB.LinComb c'.P q' ε) :=
      GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q' ε
    have h1 := pull_isLB P.isLB φ
    have h2 := pull_isLB l0 φ
    exact LBIso.trans P'.isLB h1 l3 hL (LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5)))

  have wε : ∀ E, (φ ≫ (ε E).left) ≫ P.A.hom = P'.A.hom ≫ f := fun E => by
    rw [Category.assoc, Over.w, hφp.w]
  let ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A) := fun E =>
    Over.homMk (hφp.lift (φ ≫ (ε E).left) P'.A.hom (wε E)) (hφp.lift_snd _ _ _)
  have hε'φ : ∀ E, (ε' E).left ≫ φ = φ ≫ (ε E).left := fun E => hφp.lift_fst _ _ _
  let U : Over.mk (P'.A.hom ≫ f) ⟶ P.A := pushPt hφ.1.w (𝟙 P'.A)
  have hUl : U.left = φ := by
    simp [U, pushPt]
  have hpushε : ∀ E, pushPt hφ.1.w (ε' E) = U ≫ ε E := fun E => Over.OverMorphism.ext (by
    show (ε' E).left ≫ φ = U.left ≫ (ε E).left
    rw [hUl, hε'φ])
  have hpushpr : ∀ b, pushPt hψ.1.w (pr' b) = U ≫ pr b := fun b => by
    rw [← push_comp]; simp
  refine ⟨ε', ⟨c', hc'u, pr', hmon, huniv', hbun', fun E a => injψ ?_⟩, hε'φ⟩
  rw [push_comp, hpushε, Category.assoc, hdiag E a]
  change preHom (G := c.A) U _ = pushHom hψ P'.A _
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp_apply, map_zpow]
  congr 1
  exact (hpushpr b).symm

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBas
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section General

variable {A : Type} [Ring A]

theorem span_mul_mem {S : Set A} (h : ∀ s ∈ S, ∀ y, s * y ∈ Ideal.span S) {x : A} (hx : x ∈ Ideal.span S) (y : A) :
    x * y ∈ Ideal.span S := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx y
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul r x _ ih => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ ih

theorem span_map_mem (f : A →+* A) {S : Set A} (h : ∀ s ∈ S, f s ∈ Ideal.span S) {x : A} (hx : x ∈ Ideal.span S) :
    f x ∈ Ideal.span S := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul r x _ ih => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ ih

theorem sup_mul_mem {I K : Ideal A} (hI : ∀ x ∈ I, ∀ y, x * y ∈ I) (hK : ∀ x ∈ K, ∀ y, x * y ∈ K) {x : A}
    (hx : x ∈ I ⊔ K) (y : A) : x * y ∈ I ⊔ K := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [add_mul]
  exact add_mem (Ideal.mem_sup_left (hI a ha y)) (Ideal.mem_sup_right (hK b hb y))

theorem sup_map_mem (f : A →+* A) {I K : Ideal A} (hI : ∀ x ∈ I, f x ∈ I) (hK : ∀ x ∈ K, f x ∈ K) {x : A}
    (hx : x ∈ I ⊔ K) : f x ∈ I ⊔ K := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _)]
  exact add_mem (Ideal.mem_sup_left (hI a ha)) (Ideal.mem_sup_right (hK b hb))

end General

section Filt

variable {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J)

theorem fil_anti' {m n : ℕ} (h : m ≤ n) : fil δ n ≤ fil δ m :=
  Ideal.span_mono fun _ ⟨l, h1, h2, h3⟩ ↦ ⟨l, h1, h.trans h2, h3⟩

theorem fil_mul_mem' {m n : ℕ} {a b : B} (ha : a ∈ fil δ m) (hb : b ∈ fil δ n) : a * b ∈ fil δ (m + n) := by
  have key : fil δ m * fil δ n ≤ fil δ (m + n) := by
    rw [fil, fil, Ideal.span_mul_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨x, ⟨l, hl, hs, rfl⟩, y, ⟨l', hl', hs', rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨l ++ l', fun p hp ↦ ?_, ?_, ?_⟩
    · rcases List.mem_append.1 hp with hp | hp
      exacts [hl p hp, hl' p hp]
    · simp only [List.map_append, List.sum_append]; omega
    · simp only [List.map_append, List.prod_append]
  exact key (Ideal.mul_mem_mul ha hb)

end Filt

section Main

variable (R : Type) [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

def relGen : Set (DR R B) :=
  {x | ∃ n : ℕ, ∃ a ∈ J, x = ι1 (D R B (δ.dpow (n + 1) a) - δ.dpow n a • D R B a)}

theorem rel_eq_span : rel R δ = Ideal.span (relGen R δ) := rfl

theorem rel_mul_mem {x : DR R B} (hx : x ∈ rel R δ) (y : DR R B) : x * y ∈ rel R δ := by
  rw [rel_eq_span] at hx ⊢
  refine span_mul_mem (fun s hs y ↦ ?_) hx y
  obtain ⟨n, a, ha, rfl⟩ := hs
  rw [ι_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, a, ha, rfl⟩)

theorem sgn_mem_rel {x : DR R B} (hx : x ∈ rel R δ) : sgn x ∈ rel R δ := by
  rw [rel_eq_span] at hx ⊢
  refine span_map_mem (sgn : DR R B →ₐ[B] DR R B).toRingHom (fun s hs ↦ ?_) hx
  obtain ⟨n, a, ha, rfl⟩ := hs
  change sgn (ι1 _) ∈ _
  rw [sgn_ι]
  exact neg_mem (Ideal.subset_span ⟨n, a, ha, rfl⟩)

theorem filSpan_mul_mem (n : ℕ) {x : DR R B} (hx : x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n))
    (y : DR R B) : x * y ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n) := by
  refine span_mul_mem (fun s hs y ↦ ?_) hx y
  obtain ⟨b, hb, rfl⟩ := hs
  rw [Algebra.commutes]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, hb, rfl⟩)

theorem filSpan_sgn_mem (n : ℕ) {x : DR R B} (hx : x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n)) :
    sgn x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n) := by
  refine span_map_mem (sgn : DR R B →ₐ[B] DR R B).toRingHom (fun s hs ↦ ?_) hx
  obtain ⟨b, hb, rfl⟩ := hs
  change sgn (algebraMap B _ b) ∈ _
  rw [AlgHom.commutes]
  exact Ideal.subset_span ⟨b, hb, rfl⟩

theorem filSpan_smul_mem (m n : ℕ) {b : B} (hb : b ∈ fil δ m) {x : DR R B}
    (hx : x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n)) :
    b • x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ (m + n)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    rw [Algebra.smul_def, ← map_mul]
    exact Ideal.subset_span ⟨b * c, fil_mul_mem' δ hb hc, rfl⟩
  | zero => simp
  | add x z _ _ hx hz => rw [smul_add]; exact add_mem hx hz
  | smul r x _ ih =>
    rw [smul_eq_mul, Algebra.smul_def, ← mul_assoc, Algebra.commutes b r, mul_assoc, ← Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ ih

theorem rel_filDR_properties :
    (∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) ∧ (∀ x ∈ rel R δ, sgn x ∈ rel R δ) ∧
    (∀ n, ∀ x ∈ filDR R δ n, ∀ y, x * y ∈ filDR R δ n) ∧ (∀ n, ∀ x ∈ filDR R δ n, sgn x ∈ filDR R δ n) ∧
    filDR R δ 0 = ⊤ ∧ (∀ m n, m ≤ n → filDR R δ n ≤ filDR R δ m) ∧
    ∀ m n, ∀ b ∈ fil δ m, ∀ x ∈ filDR R δ n, b • x ∈ filDR R δ (m + n) := by
  refine ⟨fun x hx y ↦ rel_mul_mem R δ hx y, fun x hx ↦ sgn_mem_rel R δ hx, fun n x hx y ↦ ?_, fun n x hx ↦ ?_,
    ?_, fun m n h ↦ ?_, fun m n b hb x hx ↦ ?_⟩
  · exact sup_mul_mem (fun x hx y ↦ filSpan_mul_mem R δ n hx y) (fun x hx y ↦ rel_mul_mem R δ hx y) hx y
  · exact sup_map_mem (sgn : DR R B →ₐ[B] DR R B).toRingHom (fun x hx ↦ filSpan_sgn_mem R δ n hx)
      (fun x hx ↦ sgn_mem_rel R δ hx) hx
  · refine (Ideal.eq_top_iff_one _).2 (Ideal.mem_sup_left (Ideal.subset_span ⟨1, ?_, map_one _⟩))
    rw [fil_zero_eq_top]; trivial
  · exact sup_le_sup_right (Ideal.span_mono (Set.image_mono (fil_anti' δ h))) _
  · obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine add_mem (Ideal.mem_sup_left (filSpan_smul_mem R δ m n hb ha)) (Ideal.mem_sup_right ?_)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ hc


attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler in
theorem rel_eq_bot_of_map (I : Ideal R) (κ : DividedPowers I) (h : IsDPMorphism κ δ (algebraMap R B))
    (hJ : J ≤ I.map (algebraMap R B)) : rel R δ = ⊥ := by
  have hD := GlobalTheory.CrysConn.isDPDer_of_map h hJ (D R B)
  rw [rel, Ideal.span_eq_bot]
  rintro _ ⟨n, a, ha, rfl⟩
  rw [hD n a ha, sub_self, map_zero]

end Main

theorem rel_two_sided_and_bot :
    (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J),
      (∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) ∧ (∀ x ∈ rel R δ, sgn x ∈ rel R δ) ∧
      (∀ n, ∀ x ∈ filDR R δ n, ∀ y, x * y ∈ filDR R δ n) ∧ (∀ n, ∀ x ∈ filDR R δ n, sgn x ∈ filDR R δ n) ∧
      filDR R δ 0 = ⊤ ∧ (∀ m n, m ≤ n → filDR R δ n ≤ filDR R δ m) ∧
      ∀ m n, ∀ b ∈ fil δ m, ∀ x ∈ filDR R δ n, b • x ∈ filDR R δ (m + n)) ∧
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (I : Ideal R)
      (κ : DividedPowers I), IsDPMorphism κ δ (algebraMap R B) → J ≤ I.map (algebraMap R B) → rel R δ = ⊥ :=
  ⟨fun R _ _ _ _ _ δ ↦ rel_filDR_properties R δ, fun R _ _ _ _ _ δ I κ h hJ ↦ rel_eq_bot_of_map R δ I κ h hJ⟩

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointPreimageTopOfReduction
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem evalSectionAtPointOrZero_specMap_comp (Y : Scheme.{0}) (D D' : Type) [CommRing D] [CommRing D'] (φ : D →+* D') (x : Sp D ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)) (h : ⊤ ≤ x ⁻¹ᵁ U) : evU (spMap φ ≫ x) U a = φ (evU x U a) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ ↦ h (Set.mem_univ _)
  unfold evU
  rw [dite_eq_left h', dite_eq_left h]
  unfold GlobalTheory.Cris.evalAt
  rw [← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
  have e := congrArg (fun k => k.hom (x.appLE U ⊤ h a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [RingHom.comp_apply, CommRingCat.comp_apply] at e ⊢
  exact e

theorem evalSectionAtPointOrZero_restriction (Y : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (U V : Y.Opens) (h : V ≤ U) (a : Γ(Y, U)) (hV : ⊤ ≤ x ⁻¹ᵁ V) : evU x V ((Y.presheaf.map (homOfLE h).op).hom a) = evU x U a := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := hV.trans (fun p hp ↦ h hp)
  unfold evU
  rw [dite_eq_left hV, dite_eq_left hU]
  unfold GlobalTheory.Cris.evalAt
  have e := congrArg (fun k => k.hom a) (Scheme.Hom.map_appLE x hV (homOfLE h).op)
  simp only [RingHom.comp_apply, CommRingCat.comp_apply] at e ⊢
  rw [e]

theorem dualNumberSndMulInverseFst_mul_units (D : Type) [CommRing D] (u u' : DualNumber D) (hu : IsUnit u) (hu' : IsUnit u') : dl (u * u') = dl u + dl u' := by
  obtain ⟨v, hv⟩ := hu.map (TrivSqZeroExt.fstHom D D D)
  obtain ⟨v', hv'⟩ := hu'.map (TrivSqZeroExt.fstHom D D D)
  simp only [TrivSqZeroExt.fstHom_apply] at hv hv'
  unfold dl
  rw [TrivSqZeroExt.fst_mul, DualNumber.snd_mul, ← hv, ← hv', ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, Ring.inverse_unit]
  rw [mul_inv_rev, Units.val_mul]
  have a1 : (v : D) * ↑v⁻¹ = 1 := Units.mul_inv v
  have a2 : (v' : D) * ↑v'⁻¹ = 1 := Units.mul_inv v'
  linear_combination (u'.snd * ↑v'⁻¹) * a1 + (u.snd * ↑v⁻¹) * a2

theorem dualNumberAlgHomMap_fst_snd_logDerivative (R D D' : Type) [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (u : DualNumber D) : (epsHom φ u).fst = φ u.fst ∧ (epsHom φ u).snd = φ u.snd ∧ (IsUnit u → dl (epsHom φ u) = φ (dl u)) := by
  have h1 : (epsHom φ u).fst = φ u.fst := by
    simp [epsHom, DualNumber.lift_apply_apply]
  have h2 : (epsHom φ u).snd = φ u.snd := by
    simp [epsHom, DualNumber.lift_apply_apply]
  refine ⟨h1, h2, fun hu ↦ ?_⟩
  obtain ⟨v, hv⟩ := hu.map (TrivSqZeroExt.fstHom D D D)
  simp only [TrivSqZeroExt.fstHom_apply] at hv
  unfold dl
  rw [h1, h2, ← hv, Ring.inverse_unit, map_mul]
  have : φ (v : D) = ((Units.map (φ : D →* D') v : D'ˣ) : D') := rfl
  rw [this, Ring.inverse_unit]
  rfl
theorem evalSectionAtPointOrZero_schemeHom_app (Y Z : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)) : evU x (q ⁻¹ᵁ U) ((q.app U).hom a) = evU (x ≫ q) U a := by
  unfold evU
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (x ≫ q) ⁻¹ᵁ U := h
    rw [dite_eq_left h, dite_eq_left h']
    unfold GlobalTheory.Cris.evalAt
    simp only [RingHom.comp_apply]
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  · have h' : ¬ ⊤ ≤ (x ≫ q) ⁻¹ᵁ U := h
    rw [dite_eq_right h, dite_eq_right h']

theorem dualNumberPoint_preimage_top_of_reduction (Y : Scheme.{0}) (D : Type) [CommRing D] (y : Sp (DualNumber D) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom D D D).toRingHom ≫ y) ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  let f : DualNumber D →+* D := (TrivSqZeroExt.fstHom D D D).toRingHom
  have hf : Function.Surjective f := fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩
  intro p _
  change PrimeSpectrum (DualNumber D) at p
  have hp : p ∈ Set.range (PrimeSpectrum.comap f) := by
    rw [range_comap_of_surjective D f hf, PrimeSpectrum.mem_zeroLocus]
    intro z hz
    change z.fst = 0 at hz
    have hz₂ : z ^ 2 = 0 := by
      rw [pow_two]
      apply TrivSqZeroExt.ext <;> simp [hz]
    exact p.isPrime.mem_of_pow_mem 2 (hz₂ ▸ p.asIdeal.zero_mem)
  obtain ⟨q, hq⟩ := hp
  exact hq ▸ h (Set.mem_univ q)

theorem evU_dl_rules : (∀ (Y : Scheme.{0}) (D D' : Type) [CommRing D] [CommRing D'] (φ : D →+* D') (x : Sp D ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)), ⊤ ≤ x ⁻¹ᵁ U → evU (spMap φ ≫ x) U a = φ (evU x U a)) ∧ (∀ (Y : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (U V : Y.Opens) (h : V ≤ U) (a : Γ(Y, U)), ⊤ ≤ x ⁻¹ᵁ V → evU x V ((Y.presheaf.map (homOfLE h).op).hom a) = evU x U a) ∧ (∀ (Y Z : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)), evU x (q ⁻¹ᵁ U) ((q.app U).hom a) = evU (x ≫ q) U a) ∧ (∀ (D : Type) [CommRing D] (u u' : DualNumber D), IsUnit u → IsUnit u' → dl (u * u') = dl u + dl u') ∧ (∀ (R D D' : Type) [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (u : DualNumber D), (epsHom φ u).fst = φ u.fst ∧ (epsHom φ u).snd = φ u.snd ∧ (IsUnit u → dl (epsHom φ u) = φ (dl u))) ∧ ∀ (Y : Scheme.{0}) (D : Type) [CommRing D] (y : Sp (DualNumber D) ⟶ Y) (U : Y.Opens), ⊤ ≤ (spMap (TrivSqZeroExt.fstHom D D D).toRingHom ≫ y) ⁻¹ᵁ U → ⊤ ≤ y ⁻¹ᵁ U :=
  ⟨evalSectionAtPointOrZero_specMap_comp, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_schemeHom_app, dualNumberSndMulInverseFst_mul_units, dualNumberAlgHomMap_fst_snd_logDerivative, dualNumberPoint_preimage_top_of_reduction⟩

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInCompleteDVRsFiniteResidue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem dvd_of_forall_fintrait : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [Algebra.FiniteType ℤ A] (a f : A), f ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∀ t : A →+* V, t f ≠ 0 → t f ∣ t a) → f ∣ a := by
  intro A _ _ _ _ _ a f hf H
  rcases eq_or_ne a 0 with rfl | ha
  · exact dvd_zero f
  let K := FractionRing A
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have haK : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha
  have hfK : algebraMap A K f ≠ 0 := (map_ne_zero_iff _ hinj).2 hf
  let y : K := algebraMap A K f / algebraMap A K a
  have hy : y ≠ 0 := div_ne_zero hfK haK
  let S := Algebra.adjoin A {y}
  let z : S := ⟨y, Algebra.self_mem_adjoin_singleton A y⟩
  by_cases hz : IsUnit z
  · obtain ⟨w, hw⟩ := hz.exists_right_inv
    have hw' : (w : K) = y⁻¹ := eq_inv_of_mul_eq_one_right (congrArg Subtype.val hw)
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      (GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv y hy (hw' ▸ w.2))
    refine ⟨r, hinj ?_⟩
    rw [map_mul, hr, inv_div, mul_div_cancel₀ _ hfK]
  · exfalso
    have hft : Algebra.FiniteType A S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton y)
    haveI hftZ : @Algebra.FiniteType ℤ S _ _ (Ring.toIntAlgebra S) := by
      have h2 := Algebra.FiniteType.trans (R := ℤ) (S := A) (A := S) inferInstance hft
      convert h2 using 1 <;> first | rfl | exact Subsingleton.elim _ _
    have hinjS : Function.Injective (algebraMap A S) := fun b c h => hinj (congrArg Subtype.val h)
    have : CharZero S := charZero_of_injective_algebraMap hinjS
    obtain ⟨n, hn, hzn⟩ := exists_max_ideal_of_mem_nonunits hz
    have hfS : algebraMap A S f ≠ 0 := (map_ne_zero_iff _ hinjS).2 hf
    obtain ⟨V, _, _, _, _, t, hc, hfin, htf, hcomap⟩ := _root_.GlobalTheory.exists_trait_finite_residueField_charZero_avoiding S n (algebraMap A S f) hn hfS
    have hdiv := H V hc hfin (t.comp (algebraMap A S)) htf
    simp only [RingHom.comp_apply] at hdiv
    have hfa : algebraMap A S f = z * algebraMap A S a := by
      apply Subtype.ext
      show algebraMap A K f = (algebraMap A K f / algebraMap A K a) * algebraMap A K a
      rw [div_mul_cancel₀ _ haK]
    have htz : t z ∈ IsLocalRing.maximalIdeal V := by
      rw [← Ideal.mem_comap, hcomap]; exact hzn
    rw [hfa, map_mul] at hdiv htf
    obtain ⟨c, hc'⟩ := hdiv
    have hta : t (algebraMap A S a) ≠ 0 := right_ne_zero_of_mul htf
    have h1 : t z * c = 1 := by
      apply mul_left_cancel₀ hta
      calc t (algebraMap A S a) * (t z * c) = t z * t (algebraMap A S a) * c := by ring
        _ = t (algebraMap A S a) := hc'.symm
        _ = t (algebraMap A S a) * 1 := (_root_.mul_one _).symm
    exact (IsLocalRing.mem_maximalIdeal _).1 htz ⟨⟨t z, c, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end GlobalTheory.KeyEven
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrComapFiniteIndexEssFiniteTypeComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem restrict_dvr_essFiniteType : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V), ((φ.comp c).codRestrict V hc).EssFiniteType → IsDiscreteValuationRing (V.comap φ) ∧ (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  have hL0 := _root_.GlobalTheory.valuationSubring_fractions_of_essFiniteType
  have hL1 := GlobalTheory.T.isDVR_valuationSubring_comap_of_finiteDimensional
  have hL2 := GlobalTheory.T.dvr_eq_localization_integralClosure_comap
  have hL4 := _root_.GlobalTheory.fractions_unit_denominators_replace_generators
  have hL3 := GlobalTheory.T.zariski_descent_dvr_trace_localisation
  intro K L _ _ φ c hfin V _ hc hV
  have hE : IsDiscreteValuationRing (V.comap φ) := hL1 K L φ hfin V
  haveI : CharZero K := RingHom.charZero_iff c.injective |>.mp inferInstance
  obtain ⟨s₀, hs₀V, hs₀⟩ := hL0 L (φ.comp c) V hc hV
  obtain ⟨t, ht, htV⟩ := hL4 L (φ.comp c) V
    (fun x => x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) s₀
    (fun x hx => hL2 K L φ hfin V hE x (hs₀V x hx)) hs₀
  exact ⟨hE, hL3 K L φ c hfin V hc t ht htV⟩

end GlobalTheory
end

