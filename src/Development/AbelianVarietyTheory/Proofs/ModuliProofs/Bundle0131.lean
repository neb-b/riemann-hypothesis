module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodLatticeInGenus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionGenus

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_eq_iff (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ ∃ y, a = b + n • y := by
  rw [tateIso_ev_eq_iff I hn]
  unfold Datum.ModN
  exact exists_congr fun y => sub_eq_iff_eq_add'

theorem exists_lift (I' : TateIso D' k Q act e) (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D'.La, ∀ a, I.ev n a = I'.ev n (f a) := by
  have hs : ∀ a, ∃ b, I'.ev n b = I.ev n a := fun a => (I'.onto n hn _).1 (tateIso_ev_pow I hn a)
  choose s hs using hs
  let N : Submodule (𝓞 E) D'.La := LinearMap.range (n • (LinearMap.id : D'.La →ₗ[𝓞 E] D'.La))
  have hN : ∀ a b : D'.La, N.mkQ a = N.mkQ b ↔ I'.ev n a = I'.ev n b := by
    intro a b
    rw [tateIso_ev_eq_iff I' hn, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
  let φ : D.La →ₗ[𝓞 E] D'.La ⧸ N :=
    { toFun := fun a => N.mkQ (s a)
      map_add' := fun a b => by
        rw [← map_add (f := _), hN, I'.add, hs, hs, hs, I.add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← map_smul, hN, I'.lin, hs, hs, I.lin] }
  have := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property N.mkQ φ N.mkQ_surjective
  refine ⟨f, fun a => ?_⟩
  have h : N.mkQ (f a) = N.mkQ (s a) := LinearMap.congr_fun hf a
  rw [(hN _ _).1 h, hs]

theorem genus_of_tateIso
    (he : ∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c')
    (I' : TateIso D' k Q act e) (I : TateIso D k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      ((∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧
      (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧
      ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧
      ∀ n, 0 < n → I.ζ n = I'.ζ n ^ ν n ∧ ∀ a, I.ev n a = I'.ev n (f n a) := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := exists_lift I' I h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℤ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · have : NeZero n := ⟨h.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n h).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n h).pow_eq_one)
      exact ⟨i, fun _ => by rw [zpow_natCast, hi]⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, ν, ⟨?_, ?_, ?_⟩, fun n hn => ⟨hν n hn, hf n hn⟩⟩
  · intro n m hn hm a
    rw [← ev_eq_iff I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun x => ?_, fun x' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨x, hx⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn x')
      refine ⟨x, (ev_eq_iff I' hn _ _).1 ?_⟩
      rw [← hf n hn, hx]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ hn (tateIso_ev_pow I' hn _) (tateIso_ev_pow I' hn _) e1 e2
    rw [hν n hn, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]

end

theorem unitOn_injective {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun a b h => by
  have h1 := congrArg (fun x : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x.val) h
  apply Units.ext
  simpa [unitOn] using h1

noncomputable def expRoot (n : ℕ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) / n)) (Complex.exp_ne_zero _)

theorem expRoot_zpow (n : ℕ) (m : ℤ) :
    ((expRoot n ^ m : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n) := by
  rw [Units.val_zpow_eq_zpow_val, expRoot, Units.val_mk0, ← Complex.exp_int_mul]
  congr 1
  ring

theorem expRoot_prim {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (expRoot n) n := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  have h := (Complex.isPrimitiveRoot_exp n hn.ne').inv
  rw [← Complex.exp_neg] at h
  rw [expRoot, Units.val_mk0, neg_div]
  exact h

theorem expRoot_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : expRoot (n * m) ^ m = expRoot n := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, expRoot, expRoot, Units.val_mk0, Units.val_mk0, ← Complex.exp_nat_mul]
  congr 1
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

section

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

end

noncomputable def periodTateIso {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H)
    {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (act : OAct (𝓞 E) A)
    (Q : D'.La →+ (Fin g → ℂ)) (hQ : Function.Injective Q) (hΛ : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range)
    (hact : ∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a)
    (hW : ∀ (n : ℕ) (a b : D'.La) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / n) →
      Out.WeilIs A L n (u.ex ((n : ℂ)⁻¹ • Q a)) (u.ex ((n : ℂ)⁻¹ • Q b)) (unitOn c)) :
    TateIso D' ℂ (𝟙_ (Over (Sp ℂ)) ⟶ A) (fun c y => y ≫ act.act c)
      (fun n y y' c => Out.WeilIs A L n y y' (unitOn c)) where
  ζ := expRoot
  ζ_prim _ hn := expRoot_prim hn
  ζ_pow _ _ hn hm := expRoot_pow hn hm
  ev n x := u.ex ((n : ℂ)⁻¹ • Q x)
  add n a b := by rw [map_add (f := _), smul_add, u.ex_add]
  lin n c a := hact c n a
  ker n hn a := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [u.ker, hΛ]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, hQ ?_⟩
      rw [map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hn', one_smul]
    · rintro ⟨b, rfl⟩
      refine ⟨b, ?_⟩
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn', one_smul]
  onto n hn x := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := u.ex_onto x
      rw [← ex_nsmul, u.ker, hΛ] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [ha, smul_smul, inv_mul_cancel₀ hn', one_smul]⟩
    · rintro ⟨a, rfl⟩
      rw [← ex_nsmul, u.ker, hΛ, smul_smul, mul_inv_cancel₀ hn', one_smul]
      exact ⟨a, rfl⟩
  tower n m hn hm a := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [← ex_nsmul, smul_smul]
    congr 2
    push_cast
    field_simp
  isom n hn a b := hW n a b _ hn (expRoot_zpow n _)

theorem period_lattice_in_genus :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (D' : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (Q : D'.La →+ (Fin P.g → ℂ)), D'.p = D.p → D'.q = D.q → u.IsAH Hm χ → Function.Injective Q → (∀ z, z ∈ u.Λ ↔ z ∈ Q.range) → (∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a) → ∀ I : TateIso D ℂ (Over.mk (𝟙 (Sp ℂ)) ⟶ P.A) (fun c y => y ≫ act.act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧ ∀ n : ℕ, 0 < n → (I.ζ n : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n) ∧ ∀ x, (I.ev n x).left = (u.ex ((n : ℂ)⁻¹ • Q (f n x))).left := by
  intro hL hL2 hT hU E _ _ _ H D D' P u Hm χ act Q hp hq hAH hQ hΛ hE hact I
  obtain ⟨Ef, hEf, -, -, -, -, -, -, hW⟩ := _root_.GlobalTheory.AnyAppellHumbert.isAH_properties hL hL2 hT hU P u Hm χ hAH
  have hW' : ∀ (n : ℕ) (a b : D'.La) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • Q a)) (u.ex ((n : ℂ)⁻¹ • Q b)) (unitOn c) := by
    intro n a b c hn hc
    refine hW n ⟨Q a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hΛ _).2 ⟨b, rfl⟩⟩ c hn ?_
    have h := hEf ⟨Q a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hΛ _).2 ⟨b, rfl⟩⟩
    rw [hE] at h
    rw [Int.cast_injective h]
    exact hc
  obtain ⟨f, ν, ⟨h1, h2, h3⟩, h4⟩ := genus_of_tateIso (D := D) (D' := D')
    (fun n x y c c' _ hx hy ha hb =>
      unitOn_injective (((hL.weil _ P n (Over.mk (𝟙 (Sp ℂ)))).1 x y hx hy).unique ha hb))
    (periodTateIso D' u act Q hQ hΛ hact hW') I
  refine ⟨f, ν, ⟨hp, hq, h1, h2, h3⟩, fun n hn => ⟨?_, fun x => ?_⟩⟩
  · rw [(h4 n hn).1]
    exact expRoot_zpow n _
  · rw [(h4 n hn).2]
    rfl

end GlobalTheory.TorsionGenus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.FormPoly

open GlobalTheory.CechPic Polynomial

theorem poly_induction {p : ℤ[X] → Prop} (h1 : p 1) (hadd : ∀ F G, p F → p G → p (F + G))
    (hneg : ∀ F, p F → p (-F)) (hX : ∀ F, p F → p (X * F)) (F : ℤ[X]) : p F := by
  have h0 : p 0 := by simpa using hadd 1 (-1) h1 (hneg 1 h1)
  have hC : ∀ a : ℤ, p (Polynomial.C a) := by
    intro a
    induction a using Int.induction_on with
    | zero => simpa using h0
    | succ i ih => simpa using hadd _ _ ih h1
    | pred i ih => simpa [sub_eq_add_neg] using hadd _ _ ih (hneg 1 h1)
  have hmono : ∀ (n : ℕ) (a : ℤ), p (Polynomial.monomial n a) := by
    intro n a
    induction n with
    | zero => simpa using hC a
    | succ n ih => rw [← Polynomial.X_mul_monomial]; exact hX _ ih
  induction F using Polynomial.induction_on' with
  | add F G hF hG => exact hadd _ _ hF hG
  | monomial n a => exact hmono n a

theorem exists_apply {V : Type} [CommGroup V] (c : V → V) (hc : ∀ a b, c (a * b) = c a * c b) (v : V) :
    ∃ ev : ℤ[X] → V, ev 1 = v ∧ (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (X * F) = c (ev F) := by
  let φ : Module.End ℤ (Additive V) :=
    (AddMonoidHom.mk' (fun a => Additive.ofMul (c a.toMul)) (fun a b => by simp [hc])).toIntLinearMap
  refine ⟨fun F => (Polynomial.aeval φ F (Additive.ofMul v)).toMul, by simp, fun F G => by simp, fun F => by simp [φ]⟩

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem exists_ev (s : A ⟶ A) [IsMonHom s] : ∃ ev : ℤ[X] → (A ⟶ A), ev 1 = 𝟙 A ∧
    (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (X * F) = ev F ≫ s := by
  exact exists_apply (fun f => f ≫ s) (fun a b => MonObj.mul_comp a b s) (𝟙 A)

section Ev

variable {s : A ⟶ A} [IsMonHom s] {ev : ℤ[X] → (A ⟶ A)} (h1 : ev 1 = 𝟙 A)
  (hadd : ∀ F G, ev (F + G) = ev F * ev G) (hX : ∀ F, ev (X * F) = ev F ≫ s)

include hadd in
theorem ev_neg (F : ℤ[X]) : ev (-F) = (ev F)⁻¹ := by
  have h0 : ev 0 = 1 := by
    have e := hadd 0 0
    rw [add_zero] at e
    exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)
  have e := hadd F (-F)
  rw [add_neg_cancel, h0] at e
  exact eq_inv_of_mul_eq_one_right e.symm

include h1 hadd hX

theorem ev_isMonHom (F : ℤ[X]) : IsMonHom (ev F) := by
  refine poly_induction (p := fun F => IsMonHom (ev F)) ?_ ?_ ?_ ?_ F
  · rw [h1]; infer_instance
  · intro F G hF hG; rw [hadd, Hom.mul_def]; infer_instance
  · intro F hF; rw [ev_neg hadd]; infer_instance
  · intro F hF; rw [hX]; infer_instance

omit [IsMonHom s] in
theorem ev_mul (F G : ℤ[X]) : ev (F * G) = ev F ≫ ev G := by
  refine poly_induction (p := fun G => ev (F * G) = ev F ≫ ev G) ?_ ?_ ?_ ?_ G
  · rw [_root_.mul_one, h1, Category.comp_id]
  · intro G H hG hH; rw [mul_add, hadd, hadd, hG, hH, MonObj.comp_mul]
  · intro G hG; rw [mul_neg, ev_neg hadd, ev_neg hadd, hG, GrpObj.comp_inv]
  · intro G hG; rw [mul_left_comm F X G, hX, hX, hG, Category.assoc]

omit [IsMonHom s] hadd in
theorem ev_X : ev X = s := by
  have e := hX 1
  rwa [_root_.mul_one, h1, Category.id_comp] at e

end Ev

variable {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen)

include hΘ in
theorem lam_inv_left {T : Over S} (x y : T ⟶ A) : lam (cls L hL) x⁻¹ y = -lam (cls L hL) x y := by
  have e := lam_mul_left hL hΘ x x⁻¹ y
  rw [mul_inv_cancel, lam_one_left] at e
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact e.symm

include hΘ in
theorem lam_inv_right {T : Over S} (x y : T ⟶ A) : lam (cls L hL) x y⁻¹ = -lam (cls L hL) x y := by
  rw [lam_comm, lam_inv_left hL hΘ, lam_comm]


include hΘ in
theorem lam_ev_adj {s : A ⟶ A} {ev : ℤ[X] → (A ⟶ A)} (h1 : ev 1 = 𝟙 A)
    (hadd : ∀ F G, ev (F + G) = ev F * ev G) (hX : ∀ F, ev (X * F) = ev F ≫ s) {T : Over S}
    (hs : ∀ x y : T ⟶ A, lam (cls L hL) (x ≫ s) y = lam (cls L hL) x (y ≫ s)) (F : ℤ[X]) :
    ∀ x y : T ⟶ A, lam (cls L hL) (x ≫ ev F) y = lam (cls L hL) x (y ≫ ev F) := by
  have hcomm : ∀ G : ℤ[X], s ≫ ev G = ev G ≫ s := by
    intro G
    have e := ev_mul h1 hadd hX X G
    rw [ev_X h1 hX, hX] at e
    exact e.symm
  refine poly_induction (p := fun F => ∀ x y : T ⟶ A,
    lam (cls L hL) (x ≫ ev F) y = lam (cls L hL) x (y ≫ ev F)) ?_ ?_ ?_ ?_ F
  · intro x y; simp only [h1, Category.comp_id]
  · intro F G hF hG x y
    rw [hadd, MonObj.comp_mul, MonObj.comp_mul, lam_mul_left hL hΘ,
      GlobalTheory.HermTensorLB.lam_mul_right hL hΘ, hF, hG]
  · intro F hF x y
    rw [ev_neg hadd, GrpObj.comp_inv, GrpObj.comp_inv, lam_inv_left hL hΘ, lam_inv_right hL hΘ, hF]
  · intro F hF x y
    rw [hX, ← Category.assoc, hs, hF, Category.assoc, ← hcomm F]

theorem pull_one {K : Type} [Field K] {B T : Over (Sp K)} [GrpObj B] (c : Pic B.left) :
    pull (1 : T ⟶ B).left c = 0 := by
  rw [Hom.one_def, Over.comp_left, pull_comp]
  obtain ⟨N, hN, hc⟩ := cls_surj (pull η[B].left c)
  rw [← hc, (cls_eq_zero_iff hN).2 (ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_isLB_local N hN), map_zero]

private theorem isLB_cube_lemma {S : Scheme.{0}} {A T : Over S} [GrpObj A] {n : ℕ} (x : Fin n → (T ⟶ A))
    {N : LB A.left} (hN : N.IsLB) : (cubeLB A x N).IsLB :=
  ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hN _ _

private theorem lam_id_lemma_2 {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (c : Pic A.left)
    (hadd : ∀ x y z : A ⟶ A, lam c x (y * z) = lam c x y + lam c x z) :
    lam c (𝟙 A) (𝟙 A) = c + pull (GrpObj.inv : A ⟶ A).left c := by
  have e := hadd (𝟙 A) (𝟙 A) (𝟙 A)⁻¹
  rw [_root_.mul_inv_cancel, lam_one_right] at e
  have e2 : lam c (𝟙 A) (𝟙 A)⁻¹ = -c - pull (GrpObj.inv : A ⟶ A).left c := by
    unfold lam
    rw [_root_.mul_inv_cancel, pull_one, ← GrpObj.inv_eq_inv, Over.id_left, pull_id]
    abel
  rw [e2, eq_comm, add_eq_zero_iff_eq_neg] at e
  rw [e]
  abel

private theorem pull_inv_lemma_3 {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (h : Out.Sym A L) : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
  obtain ⟨U, hU, t, ht⟩ := h (IsLocalRing.closedPoint K)
  have hV : A.hom ⁻¹ᵁ U = ⊤ := by
    rw [ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem U hU]
    simp
  have h0 := (cls_eq_zero_iff (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hL _ _)).2 ⟨t, ht⟩
  rw [cls_linComb hL, Fin.sum_univ_two] at h0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul,
    ← sub_eq_add_neg, sub_eq_zero, pull_comp] at h0
  have hf : (A.left.topIso.inv ≫ (A.left.isoOfEq hV.symm).hom) ≫ (A.hom ⁻¹ᵁ U).ι = 𝟙 A.left := by
    rw [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι]
  have e := congrArg (pull (A.left.topIso.inv ≫ (A.left.isoOfEq hV.symm).hom)) h0
  rw [← pull_comp _ (A.hom ⁻¹ᵁ U).ι, ← pull_comp _ (A.hom ⁻¹ᵁ U).ι, hf, pull_id, pull_id] at e
  exact e

end GlobalTheory.FormPoly

namespace GlobalTheory

open GlobalTheory.CechPic GlobalTheory.FormPoly

theorem formPoly_bundles : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → FormIs P M s → (∃ ev : Polynomial ℤ → (P.A ⟶ P.A), ev 1 = 𝟙 P.A ∧ (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (Polynomial.X * F) = ev F ≫ s) ∧ ∀ (ev : Polynomial ℤ → (P.A ⟶ P.A)), ev 1 = 𝟙 P.A → (∀ F G, ev (F + G) = ev F * ev G) → (∀ F, ev (Polynomial.X * F) = ev F ≫ s) → (∀ F, IsMonHom (ev F)) ∧ (∀ F G, ev (F * G) = ev F ≫ ev G) ∧ (∀ F, FormIs P (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) (ev (2 * F))) ∧ (∀ F G, LBIso (cubeLB P.A ![𝟙 P.A, ev (G ^ 2 * F)] P.L) ((cubeLB P.A ![𝟙 P.A, ev (F)] P.L).pull (ev G).left)) ∧ (∀ F G, LBIso (LB.div (cubeLB P.A ![𝟙 P.A, ev (F + G)] P.L) (cubeLB P.A ![𝟙 P.A, ev (F)] P.L)) (cubeLB P.A ![𝟙 P.A, ev (G)] P.L)) ∧ LBIso (cubeLB P.A ![𝟙 P.A, ev (1)] P.L) (lbPow P.L 2) ∧ (SymB M → LBIso (cubeLB P.A ![𝟙 P.A, ev (Polynomial.X)] P.L) (lbPow M 2)) := by
  intro laws _ K _ _ P M s hM hF
  obtain ⟨hsM, hFi⟩ := hF
  have hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := by
    obtain ⟨r, hr⟩ := P.rigid
    obtain ⟨cs⟩ := (laws.cube (Sp K) P { L := P.L, rig := r, isLB := P.isLB, rigGen := hr } rfl).1
    exact ⟨cs.t, cs.isGen⟩
  have hc : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A) (N : LB P.A.left) (hN : N.IsLB),
      cls (cubeLB P.A ![x, y] N) (isLB_cube_lemma _ hN) = lam (cls N hN) x y :=
    fun x y N hN => cls_cube_two hN x y _
  have eF : lam (cls M hM) (fst P.A P.A) (snd P.A P.A) =
      lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A ≫ s) := by
    rw [← hc _ _ M hM, ← hc _ _ P.L P.isLB]
    exact (cls_eq_iff (isLB_cube_lemma _ hM) (isLB_cube_lemma _ P.isLB)).2 hFi
  have eF' : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A), lam (cls M hM) x y = lam (cls P.L P.isLB) x (y ≫ s) := by
    intro T x y
    have e := congrArg (pull (lift x y).left) eF
    rwa [pull_lam, pull_lam, lift_fst, lift_snd, lift_snd_assoc] at e
  have hsa : ∀ (T : Over (Sp K)) (x y : T ⟶ P.A),
      lam (cls P.L P.isLB) (x ≫ s) y = lam (cls P.L P.isLB) x (y ≫ s) := by
    intro T x y
    rw [lam_comm (cls P.L P.isLB) (x ≫ s) y, ← eF' y x, lam_comm (cls M hM) y x, eF' x y]
  have hMadd : ∀ x y z : P.A ⟶ P.A,
      lam (cls M hM) x (y * z) = lam (cls M hM) x y + lam (cls M hM) x z := by
    intro x y z
    rw [eF', eF', eF', MonObj.mul_comp, GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ]
  have hι := pull_inv_lemma_3 P.isLB P.sym
  refine ⟨exists_ev s, fun ev h1 hadd hX => ?_⟩
  have adj : ∀ (F : Polynomial ℤ) (T : Over (Sp K)) (x y : T ⟶ P.A),
      lam (cls P.L P.isLB) (x ≫ ev F) y = lam (cls P.L P.isLB) x (y ≫ ev F) :=
    fun F T => lam_ev_adj P.isLB hΘ h1 hadd hX (hsa T) F
  refine ⟨ev_isMonHom h1 hadd hX, ev_mul h1 hadd hX, ?_, ?_, ?_, ?_, ?_⟩
  · intro F
    have := ev_isMonHom h1 hadd hX F
    unfold FormIs
    refine ⟨ev_isMonHom h1 hadd hX (2 * F), ?_⟩
    show LBIso (cubeLB P.A ![fst P.A P.A, snd P.A P.A] (cubeLB P.A ![𝟙 P.A, ev F] P.L)) _
    rw [← cls_eq_iff (isLB_cube_lemma _ (isLB_cube_lemma _ P.isLB)) (isLB_cube_lemma _ P.isLB), hc, hc, hc,
      GlobalTheory.HermTensorLB.lam_lam P.isLB hΘ, two_mul, hadd, MonObj.comp_mul,
      GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ, Category.comp_id, Category.comp_id,
      lam_comm (cls P.L P.isLB) (snd P.A P.A), adj]
    all_goals first | exact P.isLB | exact isLB_cube_lemma _ P.isLB
  · intro F G
    rw [← cls_eq_iff (isLB_cube_lemma _ P.isLB) (pull_isLB (isLB_cube_lemma _ P.isLB) _),
      cls_pull (isLB_cube_lemma _ P.isLB), hc, hc, pull_lam, Category.comp_id]
    have e := adj G P.A (𝟙 P.A) (ev G ≫ ev F)
    rw [Category.id_comp] at e
    rw [e, show G ^ 2 * F = G * F * G by ring, ev_mul h1 hadd hX, ev_mul h1 hadd hX, Category.assoc]
    all_goals exact P.isLB
  · intro F G
    rw [← cls_eq_iff (LB.isLB_div (isLB_cube_lemma _ P.isLB) (isLB_cube_lemma _ P.isLB)) (isLB_cube_lemma _ P.isLB),
      cls_div (isLB_cube_lemma _ P.isLB) (isLB_cube_lemma _ P.isLB), hc, hc, hc, hadd,
      GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ, add_sub_cancel_left]
    all_goals exact P.isLB
  · rw [← cls_eq_iff (isLB_cube_lemma _ P.isLB) (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ P.isLB _ _), hc,
      cls_lbPow P.isLB, h1, lam_id_lemma_2 _ (fun x y z => GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ x y z), hι,
      two_nsmul]
    all_goals exact P.isLB
  · intro hsym
    have hιM : pull (GrpObj.inv : P.A ⟶ P.A).left (cls M hM) = cls M hM := by
      rw [← cls_pull hM _ (pull_isLB hM _)]
      exact ((cls_eq_iff hM (pull_isLB hM _)).2 hsym).symm
    have e := eF' (𝟙 P.A) (𝟙 P.A)
    rw [Category.id_comp] at e
    rw [← cls_eq_iff (isLB_cube_lemma _ P.isLB) (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _), hc, cls_lbPow hM,
      ev_X h1 hX, ← e, lam_id_lemma_2 _ hMadd, hιM, two_nsmul]
    all_goals exact P.isLB

end GlobalTheory
end
end

