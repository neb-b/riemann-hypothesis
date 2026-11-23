module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientNilCrystallineThickeningOfSubDPIde
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.ThickQuot

section Ring

variable {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {𝔟 : Ideal B}
  (h𝔟 : δ.IsSubDPIdeal 𝔟)
include h𝔟

theorem isSubDPIdeal_inf : δ.IsSubDPIdeal (𝔟 ⊓ J) := by
  rw [inf_eq_left.mpr h𝔟.isSubideal]; exact h𝔟

def qdp : DividedPowers (J.map (Ideal.Quotient.mk 𝔟)) :=
  DividedPowers.Quotient.dividedPowers δ (isSubDPIdeal_inf δ h𝔟)

theorem qdp_apply {n : ℕ} {a : B} (ha : a ∈ J) :
    (qdp δ h𝔟).dpow n (Ideal.Quotient.mk 𝔟 a) = Ideal.Quotient.mk 𝔟 (δ.dpow n a) :=
  DividedPowers.Quotient.dpow_apply δ (isSubDPIdeal_inf δ h𝔟) ha

theorem qdp_isDPMorphism : IsDPMorphism δ (qdp δ h𝔟) (Ideal.Quotient.mk 𝔟) :=
  DividedPowers.Quotient.isDPMorphism δ (isSubDPIdeal_inf δ h𝔟)

theorem lift_list (l : List (ℕ × (B ⧸ 𝔟))) (hl : ∀ p ∈ l, p.2 ∈ J.map (Ideal.Quotient.mk 𝔟)) :
    ∃ l' : List (ℕ × B), (∀ p ∈ l', p.2 ∈ J) ∧ l'.map Prod.fst = l.map Prod.fst ∧
      Ideal.Quotient.mk 𝔟 ((l'.map fun p ↦ δ.dpow p.1 p.2).prod) =
        (l.map fun p ↦ (qdp δ h𝔟).dpow p.1 p.2).prod := by
  induction l with
  | nil => exact ⟨[], by simp, rfl, by simp⟩
  | cons p l ih =>
    obtain ⟨l', h1, h2, h3⟩ := ih fun q hq ↦ hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨a, ha, hpa⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (hl p List.mem_cons_self)
    refine ⟨(p.1, a) :: l', ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ha
      · exact h1 q hq
    · simp [h2]
    · simp only [List.map_cons, List.prod_cons, map_mul, h3]
      rw [← hpa, qdp_apply δ h𝔟 ha]

theorem isLev_qdp {n : ℕ} (hn : IsLev δ n) : IsLev (qdp δ h𝔟) n := by
  rw [isLev_iff_prod] at hn ⊢
  intro l hl hs
  obtain ⟨l', h1, h2, h3⟩ := lift_list δ h𝔟 l hl
  rw [← h3, hn l' h1 (h2 ▸ hs), map_zero]

theorem isDPNilpotent_quotient (hδ : IsNilDP δ) : IsNilDP (qdp δ h𝔟) := by
  rw [isDPNilpotent_iff_exists_isLevel] at hδ ⊢
  obtain ⟨n, hn⟩ := hδ
  exact ⟨n, isLev_qdp δ h𝔟 hn⟩

end Ring

section Thick

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}
  (T : Thick κ t) {𝔟 : Ideal T.B} (h𝔟 : T.δ.IsSubDPIdeal 𝔟)
include h𝔟

def quot : Thick κ t where
  B := T.B ⧸ 𝔟
  J := T.J.map (Ideal.Quotient.mk 𝔟)
  δ := qdp T.δ h𝔟
  nil := isDPNilpotent_quotient T.δ h𝔟 T.nil
  dp := by
    have : algebraMap R (T.B ⧸ 𝔟) = (Ideal.Quotient.mk 𝔟).comp (algebraMap R T.B) := rfl
    rw [this]
    exact (qdp_isDPMorphism T.δ h𝔟).comp _ T.dp
  B₀ := T.B₀
  π := Ideal.Quotient.lift 𝔟 T.π fun a ha ↦ (T.ker a).2 (h𝔟.isSubideal ha)
  surj := Ideal.Quotient.lift_surjective_of_surjective _ _ T.surj
  ker b := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.lift_mk, T.ker, Ideal.mem_quotient_iff_mem h𝔟.isSubideal]
  x := T.x
  w := by
    convert T.w using 2
    exact RingHom.ext fun _ ↦ rfl

def proj : T ⟶ quot T h𝔟 where
  φ := Ideal.Quotient.mkₐ R 𝔟
  φ₀ := RingHom.id T.B₀
  comm _ := rfl
  dp := qdp_isDPMorphism T.δ h𝔟
  pt := by
    show spMap (RingHom.id T.B₀) ≫ T.x = T.x
    rw [spMap_id, Category.id_comp]

def desc {S : Thick κ t} (a : T ⟶ S) (ha : ∀ b ∈ 𝔟, a.φ b = 0) : quot T h𝔟 ⟶ S where
  φ := Ideal.Quotient.liftₐ 𝔟 a.φ ha
  φ₀ := a.φ₀
  comm b := by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact a.comm c
  dp := by
    refine ⟨?_, fun {n} y hy ↦ ?_⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro y hy
      obtain ⟨c, hc, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
      exact Thick.Hom.mem a hc
    · obtain ⟨c, hc, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
      have e1 : (quot T h𝔟).δ.dpow n (Ideal.Quotient.mk 𝔟 c) = Ideal.Quotient.mk 𝔟 (T.δ.dpow n c) :=
        qdp_apply T.δ h𝔟 hc
      rw [e1]
      exact a.dp.2 c hc
  pt := a.pt

end Thick

section Main

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem exists_quotient : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (T : Thick κ t) (𝔟 : Ideal T.B), T.δ.IsSubDPIdeal 𝔟 → ∃ (G : Thick κ t) (q : T ⟶ G), Function.Surjective q.φ ∧ (∀ b, q.φ b = 0 ↔ b ∈ 𝔟) ∧ G.J = T.J.map (q.φ : T.B →+* G.B) ∧ (∀ n, IsLev T.δ n → IsLev G.δ n) ∧ ∀ (S : Thick κ t) (a : T ⟶ S), (∀ b ∈ 𝔟, a.φ b = 0) → ∃! g : G ⟶ S, q ≫ g = a := by
  intro R _ I κ X t T 𝔟 h𝔟
  refine ⟨quot T h𝔟, proj T h𝔟, Ideal.Quotient.mkₐ_surjective R 𝔟, fun b ↦ Ideal.Quotient.eq_zero_iff_mem,
    rfl, fun n hn ↦ isLev_qdp T.δ h𝔟 hn, fun S a ha ↦
      ⟨desc T h𝔟 a ha, Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl), fun g hg ↦
        Thick.Hom.ext' (AlgHom.ext fun b ↦ ?_)⟩⟩
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact congrArg (fun f : T ⟶ S ↦ f.φ c) hg

end Main

end GlobalTheory.ThickQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFunctionMapsOfCartierTwistSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Cartier

variable {Y : Scheme.{0}} [IsIntegral Y]

def chartEqn {D : CartierDiv Y} (i : (toLB D).ι) : Y.functionFieldˣ := (show EqnChart D from i).1.2

theorem gen_mem_chart {D : CartierDiv Y} (i : (toLB D).ι) : genericPoint Y ∈ (toLB D).U i :=
  (show EqnChart D from i).2.1

theorem isEqn_chartEqn {D : CartierDiv Y} (i : (toLB D).ι) {x : Y} (hx : x ∈ (toLB D).U i) :
    D.IsEqn x (chartEqn i) :=
  (show EqnChart D from i).2.2 x hx

theorem fnOf_g_chart {D : CartierDiv Y} (i j : (toLB D).ι) (h) :
    fnOf _ h ((toLB D).g i j).val = (chartEqn i : Y.functionField) / (chartEqn j : Y.functionField) :=
  fnOf_toLB_g i j h

def genChart (D : CartierDiv Y) : (toLB D).ι :=
  (exists_chart (isLB_toLB D) (genericPoint Y)).choose

def coordFn {D : CartierDiv Y} {W : Y.Opens}
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    Γ(Y, W ⊓ (toLB D).U i) :=
  Twist.coord (sectionsOn.toΓ _ _ a) i

theorem coordFn_zero {D : CartierDiv Y} {W : Y.Opens} (i : (toLB D).ι) :
    coordFn (0 : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) i = 0 := rfl

theorem coordFn_add {D : CartierDiv Y} {W : Y.Opens}
    (a b : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    coordFn (a + b) i = coordFn a i + coordFn b i := rfl


open Classical in
def ratOn (D : CartierDiv Y) (W : Y.Opens) :
    sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField where
  toFun a := if h : genericPoint Y ∈ W then
      fnOf _ (memInf h (gen_mem_chart (genChart D))) (coordFn a (genChart D)) /
        (chartEqn (genChart D) : Y.functionField)
    else 0
  map_zero' := by
    split_ifs with h
    · rw [coordFn_zero, map_zero, zero_div]
    · rfl
  map_add' a b := by
    split_ifs with h
    · rw [coordFn_add, map_add (f := _), add_div]
    · rw [add_zero]

theorem ratOn_apply (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) :
    ratOn D W a = fnOf _ (memInf h (gen_mem_chart (genChart D))) (coordFn a (genChart D)) /
      (chartEqn (genChart D) : Y.functionField) :=
  dif_pos h

theorem ratOn_mul (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    ratOn D W a * chartEqn i = fnOf _ (memInf h (gen_mem_chart i)) (coordFn a i) := by
  set j := genChart D
  have hij : genericPoint Y ∈ W ⊓ (toLB D).U i ⊓ (toLB D).U j :=
    memInf (memInf h (gen_mem_chart i)) (gen_mem_chart j)
  have e0 : resG Y (inf_le_left : W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U i) (coordFn a i) =
      resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ (toLB D).U i ⊓ (toLB D).U j) ((toLB D).g i j).val *
        resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U j) (coordFn a j) :=
    Twist.coord_rel (sectionsOn.toΓ _ _ a) i j _ _ _
  have e := congrArg (fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij) e0
  rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, fnOf_g_chart] at e
  rw [ratOn_apply D h, e]
  have := (chartEqn j).ne_zero
  field_simp
  exact mul_comm _ _

end GlobalTheory.Cartier

namespace GlobalTheory.Cartier

variable {Y : Scheme.{0}} [IsIntegral Y]

theorem ratOn_regularAt (D : CartierDiv Y) {W : Y.Opens}
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) {y : Y} (hy : y ∈ W) :
    D.RegularAt y (ratOn D W a) := by
  obtain ⟨i, hi⟩ : ∃ i, y ∈ (toLB D).U i := exists_chart (isLB_toLB D) y
  refine ⟨chartEqn i, isEqn_chartEqn i hi, ?_⟩
  rw [ratOn_mul D (gen_mem hy) a i]
  exact regAt_fnOf (memInf hy hi) _ _

theorem exists_ratOn_eq (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    {f : Y.functionField} (hf : ∀ y ∈ W, D.RegularAt y f) :
    ∃ a, ratOn D W a = f := by
  have key (i : (toLB D).ι) : ∃ b : Γ(Y, W ⊓ (toLB D).U i),
      fnOf _ (memInf h (gen_mem_chart i)) b = f * chartEqn i :=
    exists_fnOf_eq _ fun x hx => (isEqn_chartEqn i hx.2).regularAt_iff.1 (hf x hx.1)
  choose b hb using key
  have hmem : b ∈ Twist.secGroup (GlobalTheory.structureModule Y) (toLB D) W := fun i j =>
    fn_ext (U := W ⊓ (toLB D).U i ⊓ (toLB D).U j) fun hij => by
      show fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij
          (resG Y (inf_le_left : W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U i) (b i)) =
        fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij
          (resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
              W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ (toLB D).U i ⊓ (toLB D).U j) ((toLB D).g i j).val *
            resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U j) (b j))
      rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hb, hb, fnOf_g_chart]
      have := (chartEqn j).ne_zero
      field_simp
  refine ⟨(sectionsOn.toΓ _ _).symm (Twist.mkSec b hmem), ?_⟩
  have e := ratOn_mul D h ((sectionsOn.toΓ _ _).symm (Twist.mkSec b hmem)) (genChart D)
  exact mul_right_cancel₀ (chartEqn (genChart D)).ne_zero (e.trans (hb _))

theorem ratOn_res (D : CartierDiv Y) {W W' : Y.Opens} (hle : W' ≤ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (h : genericPoint Y ∈ W') :
    ratOn D W' (sectionsOn.res Γ(Y, ⊤) _ hle a) = ratOn D W a := by
  rw [ratOn_apply D h, ratOn_apply D (hle h)]
  have e : coordFn (sectionsOn.res Γ(Y, ⊤) _ hle a) (genChart D) =
      resG Y (inf_le_inf_right _ hle) (coordFn a (genChart D)) := rfl
  rw [e, fnOf_resG]

theorem exists_ratOn_twist : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y), ∃ ρ : ∀ W : Y.Opens, sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField, (∀ (W : Y.Opens) (a), ∀ y ∈ W, D.RegularAt y (ρ W a)) ∧ (∀ (W : Y.Opens) (f : Y.functionField), genericPoint Y ∈ W → (∀ y ∈ W, D.RegularAt y f) → ∃ a, ρ W a = f) ∧ ∀ (W W' : Y.Opens) (h : W' ≤ W) (a), genericPoint Y ∈ W' → ρ W' (sectionsOn.res Γ(Y, ⊤) _ h a) = ρ W a :=
  fun Y _ D => ⟨ratOn D, fun _ a _ hy => ratOn_regularAt D a hy,
    fun _ _ h hf => exists_ratOn_eq D h hf, fun _ _ hle a h => ratOn_res D hle a h⟩

end GlobalTheory.Cartier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl

section Analytic

variable {B : NumB ℂ} {g : ℕ} (d : AB B g)

theorem ex_zero' : d.ex 0 = 1 := by
  have h := d.ex_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem autV_cube (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (x y z : Fin g → ℂ) :
    autV τ a b M N (x + y + z) * autV τ a b M N z = autV τ a b M N (x + z) * autV τ a b M N (y + z) := by
  simp only [autV, ← Complex.exp_add]
  congr 1
  simp only [dotProduct_add]
  ring

theorem autV_ne (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (w : Fin g → ℂ) :
    autV τ a b M N w ≠ 0 := Complex.exp_ne_zero _

theorem fr_shift (M N : Fin g → ℤ) (w : Fin g → ℂ) :
    (d.fr (w + perV d.τ M N) : ℂ) = d.fr w / autV d.τ d.a d.b M N w := by
  rw [d.fr_per M N w, mul_div_cancel_left₀ _ (autV_ne _ _ _ _ _ _)]

theorem cubF_per (x y : Fin g → ℂ) (M N : Fin g → ℤ) (z : Fin g → ℂ) :
    cubF d x y (z + perV d.τ M N) = cubF d x y z := by
  have hP : d.ex (perV d.τ M N) = 1 := (d.ker _).2 ⟨M, N, rfl⟩
  have e1 : x + (z + perV d.τ M N) = x + z + perV d.τ M N := by abel
  have e2 : y + (z + perV d.τ M N) = y + z + perV d.τ M N := by abel
  have e3 : x + y + (z + perV d.τ M N) = x + y + z + perV d.τ M N := by abel
  unfold cubF
  rw [d.ex_add, hP, _root_.mul_one, e1, e2, e3, fr_shift, fr_shift, fr_shift, fr_shift]
  have A := autV_cube d.τ d.a d.b M N x y z
  have h1 := autV_ne d.τ d.a d.b M N (x + z)
  have h2 := autV_ne d.τ d.a d.b M N (y + z)
  have h3 := autV_ne d.τ d.a d.b M N (x + y + z)
  have h4 := autV_ne d.τ d.a d.b M N z
  have u1 := (d.fr (x + y + z)).ne_zero
  have u2 := (d.fr x).ne_zero
  have u3 := (d.fr y).ne_zero
  have u4 := (d.fr z).ne_zero
  field_simp
  linear_combination A

end Analytic

section Bound

variable {B : NumB ℂ} {g : ℕ}

def rv (s : Fin g → ℝ) : Fin g → ℂ := fun i => (s i : ℂ)

theorem exists_real_coords (τ : Matrix (Fin g) (Fin g) ℂ) (hpos : (τ.map Complex.im).PosDef) (z : Fin g → ℂ) :
    ∃ s t : Fin g → ℝ, z = rv s + τ *ᵥ rv t := by
  have hT : IsUnit (τ.map Complex.im).det := isUnit_iff_ne_zero.2 hpos.det_pos.ne'
  set t : Fin g → ℝ := (τ.map Complex.im)⁻¹ *ᵥ (fun i => (z i).im) with ht
  refine ⟨(fun i => (z i).re) - (τ.map Complex.re) *ᵥ t, t, ?_⟩
  have hIm : (τ.map Complex.im) *ᵥ t = fun i => (z i).im := by
    rw [ht, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hT, Matrix.one_mulVec]
  funext i
  have hi := congrFun hIm i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hi
  apply Complex.ext
  · simp [rv, Matrix.mulVec, dotProduct, Complex.re_sum]
  · simp [rv, Matrix.mulVec, dotProduct, Complex.im_sum, hi]

theorem exists_reduce (d : AB B g) (z : Fin g → ℂ) : ∃ (M N : Fin g → ℤ) (s t : Fin g → ℝ),
    (∀ i, s i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) ∧ z = rv s + d.τ *ᵥ rv t + perV d.τ M N := by
  obtain ⟨s, t, rfl⟩ := exists_real_coords d.τ d.pos z
  refine ⟨fun i => ⌊s i⌋, fun i => ⌊t i⌋, fun i => Int.fract (s i), fun i => Int.fract (t i),
    fun i => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, fun i => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ?_⟩
  have hs : rv s = rv (fun i => Int.fract (s i)) + cv (fun i => ⌊s i⌋) := by
    funext i; simp only [rv, cv, Pi.add_apply, Int.fract]; push_cast; ring
  have ht : rv t = rv (fun i => Int.fract (t i)) + cv (fun i => ⌊t i⌋) := by
    funext i; simp only [rv, cv, Pi.add_apply, Int.fract]; push_cast; ring
  rw [hs, ht, perV, Matrix.mulVec_add]
  abel

theorem bounded_of_per (d : AB B g) (F : (Fin g → ℂ) → ℂ) (hc : Continuous F)
    (hper : ∀ M N z, F (z + perV d.τ M N) = F z) : Bornology.IsBounded (Set.range F) := by
  have hrv : Continuous (fun s : Fin g → ℝ => rv s) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hΦ : Continuous (fun p : (Fin g → ℝ) × (Fin g → ℝ) => rv p.1 + d.τ *ᵥ rv p.2) :=
    (hrv.comp continuous_fst).add (continuous_const.matrix_mulVec (hrv.comp continuous_snd))
  have hK : IsCompact ((Set.univ.pi fun _ : Fin g => Set.Icc (0 : ℝ) 1) ×ˢ (Set.univ.pi fun _ : Fin g => Set.Icc (0 : ℝ) 1)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.comp hΦ).continuousOn
  refine isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨M, N, s, t, hs, ht, rfl⟩ := exists_reduce d z
  rw [hper]
  exact hC (s, t) ⟨fun i _ => hs i, fun i _ => ht i⟩

theorem cub_of_diff (d : AB B g) (h : ∀ x y : Fin g → ℂ, Differentiable ℂ (cubF d x y)) : d.Cub := by
  intro x y z
  have hb := bounded_of_per d _ (h x y).continuous (cubF_per d x y)
  have e := (h x y).apply_eq_apply_of_bounded hb z 0
  have u1 := (d.fr (x + y + z)).ne_zero
  have u2 := (d.fr x).ne_zero
  have u3 := (d.fr y).ne_zero
  have u4 := (d.fr z).ne_zero
  have u5 := (d.fr (x + y)).ne_zero
  have h0 : cubF d x y 0 = 1 := by
    unfold cubF
    rw [ex_zero', B.cub.face₃, add_zero, add_zero, add_zero, d.fr_zero]
    simp only [Units.val_one, _root_.one_mul, _root_.mul_one]
    field_simp
  rw [h0] at e
  unfold cubF at e
  rw [div_eq_one_iff_eq (by simp [u1, u2, u3, u4])] at e
  apply Units.ext
  simpa only [Units.val_mul] using e

end Bound

theorem cub_of_geo : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → d.Cub := by
  intro R _ _ _ _ D hψ hτ _ N ν g d hG
  exact cub_of_diff d (_root_.GlobalTheory.MBLow.Cl.CubHol.cubF_entire R D hψ hτ N ν g d hG)

end GlobalTheory.MBLow.Cl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeFrobeniusGrpSchemeCharP
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelFrobGrp

open GlobalTheory.AbDual GlobalTheory.PDiv

variable {R R' : Type} [CommRing R] [CommRing R'] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
  {σ : R →+* R'} {φ : A'.left ⟶ A.left}

def down (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x : Y ⟶ A') :
    Over.mk (Y.hom ≫ spMap σ) ⟶ A :=
  Over.homMk (x.left ≫ φ) (by simp [m.w])

theorem down_mul (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x y : Y ⟶ A') :
    down m (x * y) = down m x * down m y :=
  Over.OverMorphism.ext (m.mul Y x y (down m x) (down m y) rfl rfl).symm

theorem main : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left), IsGrpPullback A₁ A (spMap (frobR p R hR)) π → ∃ F : A ⟶ A₁, IsMonHom F ∧ F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A) := by
  intro p _ R _ hR A A₁ _ _ π hπ
  have mF : GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A (frobR p R hR)
      (spMap (frobR p R hR)) (GlobalTheory.VB.frob A.left p (cast_left p R hR A)) := by
    refine ⟨isDPMorphism_of_eq_bot _ rfl _ _, ?_, frob_comp_hom p R hR A.hom _, ?_⟩
    · simp
    · intro T x y x₀ y₀ hx hy
      have hT : (p : Γ(T.left, ⊤)) = 0 := cast_left p R hR T
      have hn (f : T.left ⟶ A.left) :
          GlobalTheory.VB.frob T.left p hT ≫ f = f ≫ GlobalTheory.VB.frob A.left p (cast_left p R hR A) :=
        GlobalTheory.SS.FrobField.absFrob_nat f p 1 Fact.out hT _
      let j : Over.mk (T.hom ≫ spMap (frobR p R hR)) ⟶ T :=
        Over.homMk (GlobalTheory.VB.frob T.left p hT) (by simpa using frob_comp_hom p R hR T.hom hT)
      have ex : x₀ = j ≫ x := Over.OverMorphism.ext (by
        simp only [hx, Over.comp_left, Over.homMk_left, j, hn])
      have ey : y₀ = j ≫ y := Over.OverMorphism.ext (by
        simp only [hy, Over.comp_left, Over.homMk_left, j, hn])
      subst ex ey
      rw [← MonObj.comp_mul]
      simp only [Over.comp_left, Over.homMk_left, j]
      exact hn (x * y).left
  have mπ := grpMor_of_isGrpPullback hπ
  let F : A ⟶ A₁ := liftPt hπ A.hom _ mF.w
  have hF : F.left ≫ π = _ := liftPt_left hπ A.hom _ mF.w
  have dF : ∀ {Y : Over (Sp R)} (t : Y ⟶ A), down mπ (t ≫ F) = down mF t := fun t ↦
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans (congrArg (t.left ≫ ·) hF))
  refine ⟨F, isMonHom_of_mul _ fun T x y ↦ pt_ext hπ ?_, hF⟩
  have e : down mπ ((x * y) ≫ F) = down mπ ((x ≫ F) * (y ≫ F)) := by rw [down_mul, dF, dF, dF, down_mul]
  exact congrArg (fun z ↦ z.left) e

end GlobalTheory.RelFrobGrp
end
end

