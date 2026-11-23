module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuad
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.PsiFrame

theorem char_ext {X G : Type} [AddCommGroup X] [CommGroup G] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (f g : X → G)
    (hf : ∀ a b, f (a + b) = f a * f b) (hg : ∀ a b, g (a + b) = g a * g b) (h : ∀ l, f (bX l) = g (bX l)) (χ : X) :
    f χ = g χ := by
  let F : X →+ Additive G := AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) (fun a b => by simp [hf])
  let G' : X →+ Additive G := AddMonoidHom.mk' (fun x => Additive.ofMul (g x)) (fun a b => by simp [hg])
  have : F.toIntLinearMap = G'.toIntLinearMap := bX.ext fun l => by simp [F, G', h]
  have := LinearMap.congr_fun this χ
  simpa [F, G'] using this

def eu (z : ℂ) : ℂˣ := Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)

theorem eu_add (z w : ℂ) : eu (z + w) = eu z * eu w := by
  ext; simp [eu, Complex.exp_add]

theorem co_add {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (a b : X) :
    co bX (a + b) = co bX a + co bX b := by
  ext l; simp [co]

theorem co_neg {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (a : X) :
    co bX (-a) = - co bX a := by
  ext l; simp [co]

theorem co_basis {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (l : Fin r) :
    co bX (bX l) = Pi.single l 1 := by
  ext l'
  by_cases h : l' = l
  · subst h; simp [co]
  · simp [co, h, Finsupp.single_apply, Ne.symm h]

theorem exists_quad {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (Ψ : X → ℂˣ)
    (hev : ∀ a, Ψ (-a) = Ψ a)
    (hb : ∀ a a' b, Ψ (a + a' + b) / Ψ (a + a') / Ψ b = (Ψ (a + b) / Ψ a / Ψ b) * (Ψ (a' + b) / Ψ a' / Ψ b)) :
    ∃ (t : Matrix (Fin r) (Fin r) ℂ) (b2 : Fin r → ℂ), t.IsSymm ∧ Half b2 ∧ ∀ χ, (Ψ χ : ℂ) =
      Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
  classical
  set T : X → X → ℂˣ := fun a b => Ψ (a + b) / Ψ a / Ψ b with hT
  have Ts : ∀ a b, T a b = T b a := fun a b => by simp only [hT, add_comm a b, div_right_comm]
  have Tl : ∀ a a' b, T (a + a') b = T a b * T a' b := hb
  have Tr : ∀ a b b', T a (b + b') = T a b * T a b' := fun a b b' => by rw [Ts, Tl, Ts b, Ts b']
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let t : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun l l' => Complex.log (T (bX l) (bX l')) / (2 * Real.pi * Complex.I)
  have ts : t.IsSymm := by
    ext l l'; simp [t, Ts (bX l)]
  have hs : ∀ u v : Fin r → ℂ, u ⬝ᵥ t *ᵥ v = v ⬝ᵥ t *ᵥ u := fun u v => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ts.eq, dotProduct_comm]
  have TQ : ∀ a b, T a b = eu (2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b)) := by
    intro a b
    refine char_ext bX (fun a => T a b) (fun a => eu (2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b)))
      (fun _ _ => Tl _ _ _) (fun _ _ => by rw [co_add, add_dotProduct, mul_add, eu_add]) (fun l => ?_) a
    refine char_ext bX (fun b => T (bX l) b) (fun b => eu (2 * Real.pi * Complex.I * (co bX (bX l) ⬝ᵥ t *ᵥ co bX b)))
      (fun _ _ => Tr _ _ _) (fun _ _ => by rw [co_add, Matrix.mulVec_add, dotProduct_add, mul_add, eu_add])
      (fun l' => ?_) b
    ext
    have : Pi.single l 1 ⬝ᵥ t *ᵥ Pi.single l' 1 = t l l' := by simp
    simp only [co_basis, this, eu, Units.val_mk0, t, Matrix.of_apply]
    rw [mul_div_cancel₀ _ hc, Complex.exp_log (Units.ne_zero _)]
  let φ : X → ℂˣ := fun χ => Ψ χ / eu (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ))
  have φadd : ∀ a b, φ (a + b) = φ a * φ b := by
    intro a b
    have h1 : Ψ (a + b) = T a b * Ψ a * Ψ b := by
      simp only [hT]; rw [mul_right_comm, div_mul_cancel, div_mul_cancel]
    have h2 : (Real.pi * Complex.I * (co bX (a + b) ⬝ᵥ t *ᵥ co bX (a + b)) : ℂ) =
        2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b) + Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX a) +
          Real.pi * Complex.I * (co bX b ⬝ᵥ t *ᵥ co bX b) := by
      rw [co_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hs (co bX b) (co bX a)]
      ring
    simp only [φ]
    rw [h1, h2, eu_add, eu_add, ← TQ, _root_.mul_assoc, _root_.mul_assoc, mul_div_mul_left_eq_div, div_mul_div_comm]
  have φev : ∀ a, φ (-a) = φ a := fun a => by
    simp only [φ, hev, co_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  have φ0 : φ 0 = 1 := by
    have := φadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have φsq : ∀ a, (φ a : ℂ) = 1 ∨ (φ a : ℂ) = -1 := fun a => by
    have := φadd a (-a)
    rw [add_neg_cancel, φ0, φev] at this
    have h2 : (φ a : ℂ) * φ a = 1 := by rw [← Units.val_mul, ← this, Units.val_one]
    exact mul_self_eq_one_iff.1 h2
  let b2 : Fin r → ℂ := fun l => if (φ (bX l) : ℂ) = 1 then 0 else 1 / 2
  refine ⟨t, b2, ts, fun l => ?_, fun χ => ?_⟩
  · simp only [b2]; split_ifs <;> simp
  · have : φ χ = eu (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
      refine char_ext bX φ (fun χ => eu (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2))) φadd
        (fun _ _ => by rw [co_add, add_dotProduct, mul_add, eu_add]) (fun l => ?_) χ
      ext
      simp only [co_basis, single_dotProduct, _root_.one_mul, eu, Units.val_mk0, b2]
      split_ifs with h
      · simp [h]
      · rw [(φsq _).resolve_left h, show (2 * Real.pi * Complex.I * (1 / 2) : ℂ) = Real.pi * Complex.I by ring,
          Complex.exp_pi_mul_I]
    have h2 : Ψ χ = eu (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
      rw [eu_add, ← this]; simp only [φ]; rw [mul_div_cancel]
    rw [h2]; rfl

theorem exists_cd (N : NumD ℂ) (g' r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (e : AB N.toNumB g') (hc : e.Cub) (hs : e.Sym) :
    ∃ d : CD N g' r bX, d.toAB = e := by
  classical
  choose z hz using fun l => e.onto (N.c (bX l))
  let t12 : Matrix (Fin g') (Fin r) ℂ := Matrix.of fun i l => z l i
  let w : N.X → Fin g' → ℂ := fun χ => t12 *ᵥ co bX χ
  have wadd : ∀ a b, w (a + b) = w a + w b := fun a b => by simp only [w, co_add, Matrix.mulVec_add]
  have wneg : ∀ a, w (-a) = - w a := fun a => by simp only [w, co_neg, Matrix.mulVec_neg]
  have ceq : ∀ χ, N.c χ = e.ex (w χ) := by
    refine char_ext bX N.c (fun χ => e.ex (w χ)) N.c_add (fun a b => by rw [wadd, e.ex_add]) (fun l => ?_)
    rw [← hz]; congr 1
    ext i; simp [w, co_basis, t12]
  obtain ⟨t, b2, ht, hb2, h⟩ := exists_quad bX (fun χ => N.ψ χ * e.fr (w χ))
    (fun a => by
      have h1 := N.even a
      have h2 := hs (w a)
      rw [wneg, ← h2, ← h1, ceq, _root_.mul_assoc])
    (fun a a' b => by
      have h1 := congrArg Additive.ofMul (N.bimult a a' b)
      have h2 := congrArg Additive.ofMul (hc (w a) (w a') (w b))
      apply Additive.ofMul.injective
      simp only [ceq, wadd, ofMul_mul, ofMul_div] at h1 h2 ⊢
      linear_combination (norm := abel) h1 - h2)
  exact ⟨{ toAB := e, cub := hc, sym := hs, t12 := t12, t22 := t, b2 := b2, toricPeriodBlock_isSymm := ht, hb2 := hb2, c_eq := ceq,
           ψ_eq := fun χ => by simpa using h χ }, rfl⟩

end GlobalTheory.MBLow.Cl.PsiFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.ProjSpace

section
variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem regAt_fnMap_of (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X) {y : Y} {t : X.functionField}
    (h : RegAt (j y) t) : RegAt y (fnMap j hη t) := by
  obtain ⟨U, hx, s, rfl⟩ := h.exists_fnOf
  have hy : y ∈ j ⁻¹ᵁ U := hx
  rw [fnMap_fnOf j hη _ (gen_mem hy)]
  exact regAt_fnOf hy _ _

theorem fnOf_appLE (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X) {U : X.Opens} {V : Y.Opens}
    (e : V ≤ j ⁻¹ᵁ U) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ V) (a : Γ(X, U)) :
    fnOf V h' ((j.appLE U V e).hom a) = fnMap j hη (fnOf U h a) := by
  rw [fnMap_fnOf j hη h (e h')]
  exact fnOf_resG e h' (j.app U a)

theorem comp_genericPoint_specializes {Z : Scheme.{0}} [IsIntegral Z] (a : Z ⟶ Y) (b : Y ⟶ X)
    (ha : a (genericPoint Z) ⤳ genericPoint Y) (hb : b (genericPoint Y) ⤳ genericPoint X) :
    (a ≫ b) (genericPoint Z) ⤳ genericPoint X := by
  rw [Scheme.Hom.comp_apply]
  exact (ha.map b.continuous).trans hb

theorem fnMap_comp {Z : Scheme.{0}} [IsIntegral Z] (a : Z ⟶ Y) (b : Y ⟶ X)
    (ha : a (genericPoint Z) ⤳ genericPoint Y) (hb : b (genericPoint Y) ⤳ genericPoint X)
    (hab : (a ≫ b) (genericPoint Z) ⤳ genericPoint X) (t : X.functionField) :
    fnMap (a ≫ b) hab t = fnMap a ha (fnMap b hb t) := by
  obtain ⟨U, hx, s, rfl⟩ := (regAt_genericPoint t).exists_fnOf
  have h1 : genericPoint Y ∈ b ⁻¹ᵁ U := hb.mem_open U.isOpen hx
  have h2 : genericPoint Z ∈ a ⁻¹ᵁ (b ⁻¹ᵁ U) := ha.mem_open (b ⁻¹ᵁ U).isOpen h1
  rw [fnMap_fnOf b hb _ h1, fnMap_fnOf a ha _ h2, fnMap_fnOf (a ≫ b) hab _ h2, Scheme.Hom.comp_app]
  rfl

theorem fnMap_congr {a b : Y ⟶ X} (e : a = b) (ha : a (genericPoint Y) ⤳ genericPoint X)
    (hb : b (genericPoint Y) ⤳ genericPoint X) (t : X.functionField) : fnMap a ha t = fnMap b hb t := by
  subst e; rfl
end

theorem exists_ratCoords : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (U : Y.Opens) (hU : (U : Set Y).Nonempty)
    (φ : U.toScheme ⟶ PSpace F N),
    haveI : Nonempty U := hU.to_subtype
    haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
    ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧
      ∀ (u : U.toScheme) (k : Fin (N + 1)) (hk : u ∈ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart F N k), w k ≠ 0 ∧ ∀ j,
        GlobalTheory.TrueGeo.SmallSec.fnMap U.ι (specializes_of_eq (genericPoint_eq_of_isOpenImmersion U.ι)) (w j / w k) =
          GlobalTheory.Cartier.fnOf (φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart F N k) (GlobalTheory.Cartier.gen_mem hk)
            (GlobalTheory.ProjSpace.pullRatio φ _ k le_rfl j) := by
  intro F _ Y _ N U hU φ
  haveI : Nonempty U := hU.to_subtype
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hηU : U.ι (genericPoint U.toScheme) ⤳ genericPoint Y :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion U.ι)
  obtain ⟨i₀, hi₀⟩ := exists_mem_chart F N (φ (genericPoint U.toScheme))
  have hg₀ : genericPoint U.toScheme ∈ φ ⁻¹ᵁ chart F N i₀ := hi₀
  choose w hw using fun j => fnMap_surjective U.ι hηU (fnOf _ hg₀ (pullRatio φ _ i₀ le_rfl j))
  refine ⟨w, i₀, ?_, fun u k hk => ?_⟩
  · apply (fnMap U.ι hηU).injective
    rw [hw, pullRatio_self, map_one, map_one]
  have hV : genericPoint U.toScheme ∈ φ ⁻¹ᵁ chart F N i₀ ⊓ φ ⁻¹ᵁ chart F N k := ⟨hg₀, gen_mem hk⟩
  have hmul : ∀ j, fnMap U.ι hηU (w j) =
      fnMap U.ι hηU (w k) * fnOf _ (gen_mem hk) (pullRatio φ _ k le_rfl j) := by
    intro j
    rw [hw, hw, ← fnOf_resG inf_le_left hV, ← fnOf_resG inf_le_left hV, ← fnOf_resG inf_le_right hV, ← map_mul,
      resG_pullRatio, resG_pullRatio, resG_pullRatio, pullRatio_mul_pullRatio]
  have hk0 : fnMap U.ι hηU (w k) ≠ 0 := by
    rw [hw, ← fnOf_resG inf_le_left hV, resG_pullRatio]
    refine ((unitAt_fnOf_iff hV hV _).2 ?_).ne_zero
    rw [basicOpen_pullRatio]
    exact ⟨hV, hV.2⟩
  refine ⟨fun h => hk0 (by rw [h, map_zero]), fun j => ?_⟩
  rw [map_div₀, hmul j, mul_div_cancel_left₀ _ hk0]

theorem exists_hom_of_ratCoords : ∀ (F : Type) [Field F] (N : ℕ) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp F)
    (w : Fin (N + 1) → Y.functionField),
    (∀ y : Y, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ g : Y ⟶ PSpace F N, g ≫ PSpace.str F N = q ∧ ∀ (y : Y) (k : Fin (N + 1)), w k ≠ 0 →
      (∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
      ∃ (W : Y.Opens) (hy : y ∈ W) (hW : W ≤ g ⁻¹ᵁ GlobalTheory.ProjSpace.chart F N k),
        ∀ j, GlobalTheory.Cartier.fnOf W (GlobalTheory.Cartier.gen_mem hy) (GlobalTheory.ProjSpace.pullRatio g W k hW j) = w j / w k := by
  intro F _ N Y _ q w hw
  classical
  have hopen : ∀ k, IsOpen {y : Y | w k ≠ 0 ∧ ∀ j, RegAt y (w j / w k)} := fun k => by
    refine isOpen_iff_forall_mem_open.2 fun y ⟨h0, hy⟩ => ?_
    obtain ⟨W, hyW, hW⟩ := GlobalTheory.InvertIdeal.exists_common_open hy
    refine ⟨W, fun y' hy' => ⟨h0, fun j => ?_⟩, W.isOpen, hyW⟩
    obtain ⟨a, ha⟩ := hW j
    exact ha ▸ regAt_fnOf hy' _ a
  let U' : Fin (N + 1) → Y.Opens := fun k => ⟨_, hopen k⟩
  have hr : ∀ k j, ∃ a : Γ(Y, U' k), ∀ h, fnOf (U' k) h a = w j / w k := fun k j => by
    by_cases h : genericPoint Y ∈ U' k
    · obtain ⟨a, ha⟩ := exists_fnOf_eq h fun y hy => hy.2 j
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose r hr using hr
  have H : IsCoordFamily U' r :=
    { cover := top_le_iff.1 fun y _ => Opens.mem_iSup.2 (hw y)
      self := fun k => fn_ext fun h => by rw [hr, map_one, div_self h.1]
      mul := fun i j k => fn_ext fun h => by
        rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hr, hr, hr]
        have hi : w i ≠ 0 := h.1.1
        have hj : w j ≠ 0 := h.2.1
        field_simp
      basicOpen_le := fun i j y hy => by
        have hyi : y ∈ U' i := Y.basicOpen_le _ hy
        have hu := (unitAt_fnOf_iff hyi (gen_mem hyi) (r i j)).2 hy
        rw [hr] at hu
        have hi0 : w i ≠ 0 := hyi.1
        have hj0 : w j ≠ 0 := fun h0 => hu.ne_zero (by rw [h0, zero_div])
        refine ⟨hj0, fun l => ?_⟩
        have := (hyi.2 l).mul hu.inv.regAt
        rwa [show w l / w i * (w j / w i)⁻¹ = w l / w j by field_simp] at this }
  refine ⟨H.toHom q, H.toHom_str q, fun y k hk0 hreg => ⟨U' k, ⟨hk0, hreg⟩, H.le_toHom_preimage q k, fun j => ?_⟩⟩
  rw [H.pullRatio_toHom q k j]
  exact hr k j _

theorem exists_ratCoords_extend : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (N : ℕ) (U : Y.Opens)
    (φ : U.toScheme ⟶ PSpace F N), φ ≫ PSpace.str F N = U.ι ≫ p → (U : Set Y).Nonempty →
    ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧
      (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        (∀ y' : Y', ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
          (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k))) →
        ∃ g : Y' ⟶ PSpace F N, g ≫ PSpace.str F N = s ≫ p ∧ (s ⁻¹ᵁ U).ι ≫ g = (s ∣_ U) ≫ φ := by
  intro F _ Y _ p N U φ hφ hU
  haveI : Nonempty U := hU.to_subtype
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hηU : U.ι (genericPoint U.toScheme) ⤳ genericPoint Y :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion U.ι)
  obtain ⟨w, i₀, hw₀, hw⟩ := exists_ratCoords F Y N U hU φ
  have loc : ∀ (u : U.toScheme) k, u ∈ φ ⁻¹ᵁ chart F N k → w k ≠ 0 ∧ ∀ j, RegAt (U.ι u) (w j / w k) := by
    intro u k hk
    refine ⟨(hw u k hk).1, fun j => ?_⟩
    rw [← regAt_fnMap_iff U.ι hηU, (hw u k hk).2 j]
    exact regAt_fnOf hk _ _
  refine ⟨w, i₀, hw₀, fun y hy => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := exists_mem_chart F N (φ ⟨y, hy⟩)
    exact ⟨k, loc ⟨y, hy⟩ k hk⟩
  intro Y' _ s hη hY'
  obtain ⟨g, hg, hgW⟩ := exists_hom_of_ratCoords F N Y' (s ≫ p) (fun j => fnMap s (specializes_of_eq hη) (w j)) hY'
  refine ⟨g, hg, hom_ext ?_ fun z => ?_⟩
  · rw [Category.assoc, hg, Category.assoc, hφ, ← Category.assoc (s ∣_ U), morphismRestrict_ι, Category.assoc]
  haveI : Nonempty (s ⁻¹ᵁ U).toScheme := ⟨z⟩
  haveI : IsIntegral (s ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (s ⁻¹ᵁ U).ι
  have hu : U.ι ((s ∣_ U) z) = s ((s ⁻¹ᵁ U).ι z) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hηι : (s ⁻¹ᵁ U).ι (genericPoint (s ⁻¹ᵁ U).toScheme) ⤳ genericPoint Y' :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion _)
  have hηr : (s ∣_ U) (genericPoint (s ⁻¹ᵁ U).toScheme) ⤳ genericPoint U.toScheme := by
    refine specializes_of_eq (U.ι.isOpenEmbedding.injective ?_)
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply,
      genericPoint_eq_of_isOpenImmersion, hη, genericPoint_eq_of_isOpenImmersion]
  obtain ⟨k, hk⟩ := exists_mem_chart F N (φ ((s ∣_ U) z))
  obtain ⟨hk0, hreg⟩ := loc _ k hk
  have hreg' : ∀ j, RegAt ((s ⁻¹ᵁ U).ι z)
      (fnMap s (specializes_of_eq hη) (w j) / fnMap s (specializes_of_eq hη) (w k)) := fun j => by
    rw [← map_div₀]
    exact regAt_fnMap_of s _ (hu ▸ hreg j)
  obtain ⟨W, hzW, hW, hWj⟩ := hgW _ k ((map_ne_zero _).2 hk0) hreg'
  have hz : z ∈ (s ⁻¹ᵁ U).ι ⁻¹ᵁ W ⊓ (s ∣_ U) ⁻¹ᵁ (φ ⁻¹ᵁ chart F N k) := ⟨hzW, hk⟩
  refine ⟨_, hz, k, inf_le_left.trans ((s ⁻¹ᵁ U).ι.preimage_mono hW), inf_le_right, fun j => ?_⟩
  refine fnOf_injective _ (gen_mem hz) ?_
  rw [← appLE_pullRatio (φ := g) (hi := hW) (s ⁻¹ᵁ U).ι inf_le_left,
    ← appLE_pullRatio (φ := φ) (hi := le_rfl) (s ∣_ U) inf_le_right,
    fnOf_appLE _ hηι _ (gen_mem hzW), fnOf_appLE _ hηr _ (gen_mem hk), hWj, ← (hw _ k hk).2 j, ← map_div₀,
    ← fnMap_comp _ _ hηι (specializes_of_eq hη) (comp_genericPoint_specializes _ _ hηι (specializes_of_eq hη)),
    ← fnMap_comp _ _ hηr hηU (comp_genericPoint_specializes _ _ hηr hηU)]
  exact fnMap_congr (morphismRestrict_ι s U).symm _ _ _

end GlobalTheory.ProjSpace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarMatrixBetweenKeyData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.TwoData

theorem exists_scalar_matrix : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (th th' : P.L.Sec) (v v' : Fin P.g → (epsR K ⟶ P.A)), (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th) → (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th') → IsLieBasis v → IsLieBasis v' → ∃ (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), a ≠ 0 ∧ (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) ∧ ∀ i, IsLieComb (M i) v (v' i) := by
  intro K _ P th th' v v' hth hth' hv hv'
  obtain ⟨b, hb⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.principalPolarisation_exists_unique_section GlobalTheory.abelianSchemeLaws_all.2.secTwist P
  obtain ⟨a, ha, -⟩ := hb th
  obtain ⟨a', ha', -⟩ := hb th'
  choose M hM using fun i => (hv.2 _ (hv'.1 i)).exists
  have hne : ∀ (s : P.L.Sec) (c : K), (∀ s' : Sp K, ∃ z : P.A.left, P.A.hom z = s' ∧ z ∈ Out.nonzeroLocus s) →
      (∀ i, s.f i = Geo.Tor.constFn P.A.hom _ c * b.f i) → c ≠ 0 := by
    rintro s c hs hc rfl
    obtain ⟨z, -, hz⟩ := hs (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    rw [hc i, Geo.Tor.constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  have h0 := hne th a hth ha
  have h0' := hne th' a' hth' ha'
  refine ⟨a' * a⁻¹, M, mul_ne_zero h0' (inv_ne_zero h0), fun i => ?_, hM⟩
  rw [ha' i, ha i, ← _root_.mul_assoc, Geo.Tor.constFn, Geo.Tor.constFn, Geo.Tor.constFn, ← map_mul, ← map_mul, inv_mul_cancel_right₀ h0]

end GlobalTheory.MBLow.TwoData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecDivNonzeroLocusEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.Cartier.RatSecDiv

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_mul_unit_iff {x : X} {a u : X.functionField} (hu : UnitAt x u) :
    UnitAt x (a * u) ↔ UnitAt x a := by
  refine ⟨fun h => ?_, fun h => h.mul hu⟩
  have e : a = a * u * u⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one]
  rw [e]; exact h.mul hu.inv

theorem local_of {D D' : CartierDiv X} {V : X.Opens} {h : X.functionField}
    (H : ∀ x : X, ∃ g g' : X.functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧
      RegAt x (h * (g : X.functionField) / (g' : X.functionField)) ∧
      (UnitAt x (h * (g : X.functionField) / (g' : X.functionField)) ↔ x ∈ V))
    {x : X} {gi rk : X.functionFieldˣ} (hi : D.IsEqn x gi) (hk : D'.IsEqn x rk) :
    RegAt x (h * (gi : X.functionField) / (rk : X.functionField)) ∧
      (UnitAt x (h * (gi : X.functionField) / (rk : X.functionField)) ↔ x ∈ V) := by
  obtain ⟨g, g', hg, hg', hr, hu⟩ := H x
  have u : UnitAt x (((gi : X.functionField) / g) * ((g' : X.functionField) / rk)) :=
    (hg.iff_unitAt.1 hi).mul (hk.iff_unitAt.1 hg')
  have e : h * (gi : X.functionField) / (rk : X.functionField) =
      h * (g : X.functionField) / (g' : X.functionField) *
        (((gi : X.functionField) / g) * ((g' : X.functionField) / rk)) := by
    have := g.ne_zero; have := g'.ne_zero; have := rk.ne_zero
    field_simp
  rw [e, unitAt_mul_unit_iff u]
  exact ⟨hr.mul u.regAt, hu⟩

end GlobalTheory.Cartier.RatSecDiv


open GlobalTheory.Cartier.RatSecDiv in
theorem GlobalTheory.Cartier.exists_sec_div_nonzeroLocus_eq :
    ∀ {X : Scheme.{0}} [IsIntegral X] (D D' : CartierDiv X) (L : LB X) (r : L.ι → X.functionFieldˣ),
    Presents D' L r → ∀ (V : X.Opens) (h : X.functionField),
    (∀ x : X, ∃ g g' : X.functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧
      RegAt x (h * (g : X.functionField) / (g' : X.functionField)) ∧
      (UnitAt x (h * (g : X.functionField) / (g' : X.functionField)) ↔ x ∈ V)) →
    ∃ θ : (LB.div (toLB D) L).Sec, nonzeroLocus θ = V := by
  intro X _ D D' L r hP V h H
  have key (p : (LB.div (toLB D) L).ι) : ∃ a : Γ(X, (LB.div (toLB D) L).U p), ∀ hp,
      fnOf _ hp a = h * (p.1.1.2 : X.functionField) / (r p.2 : X.functionField) := by
    by_cases hp : genericPoint X ∈ (LB.div (toLB D) L).U p
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hp fun x hx =>
        (local_of H (p.1.2.2 x hx.1) (hP.isEqn p.2 x hx.2)).1
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (hp h').elim⟩
  choose a ha using key
  refine ⟨⟨a, fun p q => fn_ext fun hpq => ?_⟩, ?_⟩
  · have hp : genericPoint X ∈ (LB.div (toLB D) L).U p := hpq.1
    have hq : genericPoint X ∈ (LB.div (toLB D) L).U q := hpq.2
    refine (fnOf_resG _ hpq _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg _ (fnOf_resG _ hpq _))).symm)
    rw [ha p hp, ha q hq]
    have eL := hP.isRatSec p.2 q.2 (memInf hpq.1.2 hpq.2.2)
    have e1 : fnOf _ (memInf hpq.1.1 hpq.2.1) ((toLB D).g p.1 q.1).val =
        (p.1.1.2 : X.functionField) / (q.1.1.2 : X.functionField) := fnOf_toLB_g _ _ _
    have eg : fnOf _ hpq ((LB.div (toLB D) L).g p q).val =
        fnOf _ (memInf hpq.1.1 hpq.2.1) ((toLB D).g p.1 q.1).val *
          (fnOf _ (memInf hpq.1.2 hpq.2.2) (L.g p.2 q.2).val)⁻¹ := by
      change fnOf _ hpq ((res _ ((toLB D).g p.1 q.1) * (res _ (L.g p.2 q.2))⁻¹ : Γ(X, _)ˣ).val) = _
      erw [Units.val_mul, map_mul, map_units_inv]
      exact congrArg₂ (· * ·) (fnOf_resG _ _ _) (congrArg _ (fnOf_resG _ _ _))
    have eL' : fnOf _ (memInf hpq.1.2 hpq.2.2) (L.g p.2 q.2).val =
        (r p.2 : X.functionField) / (r q.2 : X.functionField) :=
      (eq_div_of_mul_eq (r q.2).ne_zero eL.symm)
    rw [eg, e1, eL']
    have := (p.1.1.2).ne_zero; have := (q.1.1.2).ne_zero
    have := (r p.2).ne_zero; have := (r q.2).ne_zero
    field_simp
  · have hmem (p : (LB.div (toLB D) L).ι) (y : X) (hy : y ∈ (LB.div (toLB D) L).U p) :
        y ∈ X.basicOpen (a p) ↔ y ∈ V := by
      rw [← unitAt_fnOf_iff hy (gen_mem hy), ha p (gen_mem hy)]
      exact (local_of H (p.1.2.2 y hy.1) (hP.isEqn p.2 y hy.2)).2
    refine le_antisymm (iSup_le fun p y hy => (hmem p y (X.basicOpen_le _ hy)).1 hy) fun y hy => ?_
    obtain ⟨i, hi⟩ := exists_chart (isLB_toLB D) y
    obtain ⟨k, hk⟩ := exists_chart hP.isLB y
    exact Opens.mem_iSup.2 ⟨(i, k), (hmem (i, k) y ⟨hi, hk⟩).2 hy⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsVanishingOfSimplePoleMulExtendsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extends_vanishing_of_simplePole_mul_extends : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} [IsReduced Y] {O : Y.Opens}, Dense (O : Set Y) → ∀ {P B N : LB Y} (C : ProdChart P B N) (ω : H0 p P O), GlobalTheory.LogCanonicalReflexive.SimplePoleAlong O C ω → ∀ (G : H0 p N ⊤) (f : H0 p B O), H0.restr le_top G = C.mul ω f → ∃ g : H0 p B ⊤, (∀ y, y ∉ O → ∀ i hi, H0.germ i y (memTop y) hi g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) ∧ H0.restr le_top g = f := by
  first | exact @GlobalTheory.LogCanonicalReflexive.extends_vanishing_of_mul | exact GlobalTheory.LogCanonicalReflexive.extends_vanishing_of_mul | (intros; apply GlobalTheory.LogCanonicalReflexive.extends_vanishing_of_mul <;> assumption)
end

