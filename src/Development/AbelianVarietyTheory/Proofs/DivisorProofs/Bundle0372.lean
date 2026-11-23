module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveCechPoincareRichChartsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.PBFc
open GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ

variable {R : Type} [CommRing R]

abbrev BSx (X : SimplicialObject Spc) (a b : ℕ) (U : Scheme.{0}) : Type :=
  ((X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b))).obj (op U)

abbrev BSx.res {X : SimplicialObject Spc} {a b : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (y : BSx X a b U) : BSx X a b V :=
  ((X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b))).map g.op y

theorem biChains_isZero (X : SimplicialObject Spc) (c l : ℤ) (h : 0 < c ∨ 0 < l) :
    IsZero (((biChains R X).X c).X l) := by
  rcases h with h | h
  · exact (HomologicalComplex.eval _ _ l).map_isZero (HomologicalComplex.isZero_extend_X _ _ c (fun i hi => by
      change -((i : ℕ) : ℤ) = c at hi
      omega))
  · by_cases hc : c ≤ 0
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
      refine IsZero.of_iso ?_ ((HomologicalComplex.eval _ _ l).mapIso
        (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) rfl))
      exact HomologicalComplex.isZero_extend_X _ _ l (fun i hi => by
        change -((i : ℕ) : ℤ) = l at hi
        omega)
    · exact (HomologicalComplex.eval _ _ l).map_isZero (HomologicalComplex.isZero_extend_X _ _ c (fun i hi => by
        change -((i : ℕ) : ℤ) = c at hi
        omega))

def evT {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ : Cochain (totChains R X) K n) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : BSx X a b U) : Sec (K.X s) U :=
  Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ))
      (-((a + b : ℕ) : ℤ)) (by simp only [ComplexShape.π_def]; push_cast; ring) ≫ γ.v _ s h) (freeGen R _ U y)

theorem evT_ext {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ γ' : Cochain (totChains R X) K n)
    (h : ∀ a b s h U y, evT γ a b s h U y = evT γ' a b s h U y) : γ = γ' := by
  ext t s hs : 1
  apply HomologicalComplex₂.total.hom_ext
  intro c l hcl
  have hcl' : c + l = t := hcl
  by_cases hc : c ≤ 0 ∧ l ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
    obtain rfl : t = -((a + b : ℕ) : ℤ) := by push_cast; omega
    rw [← cancel_epi (biChainsXIso R X a b).inv]
    exact free_ext _ _ fun U y => h a b s hs U y
  · exact (biChains_isZero X c l (by omega)).eq_of_src _ _

theorem evT_exists {X : SimplicialObject Spc} {K : Cx R} {n : ℤ}
    (f : ∀ (a b : ℕ) (s : ℤ), -((a + b : ℕ) : ℤ) + n = s → ∀ U : Scheme.{0}, BSx X a b U → Sec (K.X s) U)
    (hf : ∀ a b s h (V U : Scheme.{0}) (g : V ⟶ U) (y : BSx X a b U), Sec.res g (f a b s h U y) = f a b s h V (y.res g)) :
    ∃ γ : Cochain (totChains R X) K n, ∀ a b s h U y, evT γ a b s h U y = f a b s h U y := by
  have key : ∀ (c l s : ℤ) (hs : c + l + n = s), ∃ ψ : ((biChains R X).X c).X l ⟶ K.X s,
      ∀ (a b : ℕ) (hc : c = -(a : ℤ)) (hl : l = -(b : ℤ)) U y,
        Sec.map ((biChainsXIso R X a b).inv ≫ eqToHom (by rw [hc, hl]) ≫ ψ) (freeGen R _ U y) =
          f a b s (by push_cast; omega) U y := by
    intro c l s hs
    by_cases hc : c ≤ 0 ∧ l ≤ 0
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (f a b s (by push_cast; omega)) (fun V U g y => hf a b s _ V U g y)
      refine ⟨(biChainsXIso R X a b).hom ≫ φ, fun a' b' hc hl U y => ?_⟩
      obtain rfl : a' = a := by omega
      obtain rfl : b' = b := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U y
    · exact ⟨0, fun a b hc' hl' => by omega⟩
  choose ψ hψ using key
  refine ⟨Cochain.mk fun t s h => (biChains R X).totalDesc fun c l hcl => ψ c l s (by
      have : c + l = t := hcl
      omega), fun a b s h U y => ?_⟩
  unfold evT
  rw [Cochain.mk_v, HomologicalComplex₂.ι_totalDesc]
  have := hψ (-(a : ℤ)) (-(b : ℤ)) s (by push_cast at h ⊢; omega) a b rfl rfl U y
  rw [eqToHom_refl, Category.id_comp] at this
  exact this

section Cross
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N))

def baseS {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) a b U) : Sx E a U :=
  (show (E.obj (op (SimplexCategory.mk a))).obj (op U) × ((Fib N).obj (op (SimplexCategory.mk b))).obj (op U) from y).1

variable {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

def vertS {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) a b U) : Sx B b U :=
  ((ℓ.app (op (SimplexCategory.mk a))).app (op (SimplexCategory.mk b))).app (op U) y

theorem baseS_res {a b : ℕ} {W U : Scheme.{0}} (g : W ⟶ U) (y : BSx (twX E V) a b U) :
    baseS V (y.res g) = (baseS V y).res g := rfl

theorem vertS_res {a b : ℕ} {W U : Scheme.{0}} (g : W ⟶ U) (y : BSx (twX E V) a b U) :
    vertS V ℓ (y.res g) = (vertS V ℓ y).res g :=
  ConcreteCategory.congr_hom (((ℓ.app (op (SimplexCategory.mk a))).app (op (SimplexCategory.mk b))).naturality g.op) y

variable {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n)
  (z : Cochain ((chains R).obj B) J m)

def crossVal (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    Sec (K.X s) U :=
  (m * (a : ℤ)).negOnePow • μ.mul U (-(a : ℤ) + n) (-(b : ℤ) + m) s (by push_cast at h; omega)
    (_root_.GlobalTheory.EtC.ev (R := R) α a _ rfl U (baseS V y))
    (_root_.GlobalTheory.EtC.ev (R := R) z b _ rfl U (vertS V ℓ y))

theorem crossVal_res (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) {W U : Scheme.{0}} (g : W ⟶ U)
    (y : BSx (twX E V) a b U) :
    Sec.res g (crossVal V ℓ μ hk α z a b s h U y) = crossVal V ℓ μ hk α z a b s h W (y.res g) := by
  unfold crossVal
  rw [Units.smul_def, Units.smul_def, Sec.res, map_zsmul, ← Sec.res, μ.nat, ev_res, ev_res, baseS_res, vertS_res]

def crossT : Cochain (totChains R (twX E V)) K k :=
  (evT_exists (crossVal V ℓ μ hk α z) (fun a b s h W U g y => crossVal_res V ℓ μ hk α z a b s h g y)).choose

theorem evT_crossT (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    evT (crossT V ℓ μ hk α z) a b s h U y =
      (m * (a : ℤ)).negOnePow • μ.mul U (-(a : ℤ) + n) (-(b : ℤ) + m) s (by push_cast at h; omega)
        (_root_.GlobalTheory.EtC.ev (R := R) α a _ rfl U (baseS V y))
        (_root_.GlobalTheory.EtC.ev (R := R) z b _ rfl U (vertS V ℓ y)) :=
  (evT_exists (crossVal V ℓ μ hk α z) (fun a b s h W U g y => crossVal_res V ℓ μ hk α z a b s h g y)).choose_spec a b s h U y

theorem evT_add {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} (γ γ' : Cochain (totChains R X) L t) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (γ + γ') a b s h U y = evT γ a b s h U y + evT γ' a b s h U y := by
  unfold evT
  rw [Cochain.add_v, Preadditive.comp_add, Preadditive.comp_add]
  exact map_add (mapHom _ _ (freeGen R _ U y)) _ _

theorem crossT_add_left (α' : Cochain ((chains R).obj E) I n) :
    crossT V ℓ μ hk (α + α') z = crossT V ℓ μ hk α z + crossT V ℓ μ hk α' z :=
  evT_ext _ _ fun a b s h U y => by
    rw [evT_add, evT_crossT, evT_crossT, evT_crossT, ev_add, map_add (f := _), LinearMap.add_apply, smul_add]

theorem evT_zero {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (0 : Cochain (totChains R X) L t) a b s h U y = 0 := by
  unfold evT
  rw [Cochain.zero_v, comp_zero, comp_zero]
  exact map_zero (mapHom _ _ (freeGen R _ U y))

theorem crossT_zero_right : crossT V ℓ μ hk α (0 : Cochain ((chains R).obj B) J m) = 0 :=
  evT_ext _ _ fun a b s h U y => by
    rw [evT_crossT, evT_zero, ev_zero, map_zero, smul_zero]

end Cross

def twPairI (q : ℕ) (i j : ℤ) : Pair (res (ZMod q) (tw q (i - j))) (res (ZMod q) (tw q j)) (res (ZMod q) (tw q i)) :=
  Eq.rec (motive := fun k _ => Pair (res (ZMod q) (tw q (i - j))) (res (ZMod q) (tw q j)) (res (ZMod q) (tw q k)))
    (twPair q (i - j) j) (sub_add_cancel i j)

def phi (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n : ℤ) :
    (∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) →+
      Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n :=
  AddMonoidHom.mk' (fun α => ∑ j : Fin N, crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) (α j) (z j))
    (fun α α' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => crossT_add_left V ℓ _ _ _ _ _)

theorem phi_apply (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n : ℤ) (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) :
    phi q V ℓ i z n α = ∑ j : Fin N, crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) (α j) (z j) := rfl

end GlobalTheory.PBFc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldEqOfModEq
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem pow_card_pow_sub_one_of_root (F : Type) [Field F] [Finite F] (f : F[X]) (hf : f.Monic)
    (hi : Irreducible f) (m : ℕ) (hd : f.natDegree ∣ m) (α : AlgebraicClosure F)
    (hα : α ∈ (f.map (algebraMap F (AlgebraicClosure F))).roots) (h0 : α ≠ 0) :
    α ^ (Nat.card F ^ m - 1) = 1 := by
  have hf0 : f.map (algebraMap F (AlgebraicClosure F)) ≠ 0 := Polynomial.map_ne_zero hi.ne_zero
  have hr : aeval α f = 0 := by
    have := (mem_roots hf0).1 hα
    rwa [IsRoot, eval_map_algebraMap] at this
  have hmin : f = minpoly F α := minpoly.eq_of_irreducible_of_monic hi hr hf
  have hx : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hfix : α ^ Nat.card F ^ m = α := by
    have h1 := ((minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := m)).1
      (by rw [← hmin]; exact hd)
    rw [minpoly.dvd_iff] at h1
    simpa [sub_eq_zero] using h1
  have hpos : 1 ≤ Nat.card F ^ m := Nat.one_le_pow _ _ Nat.card_pos
  have : α ^ (Nat.card F ^ m - 1) * α = 1 * α := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, hfix, one_mul]
  exact mul_right_cancel₀ h0 this

theorem pow_eq_pow_of_modEq' {M : Type} [Monoid M] (α : M) (N a b : ℕ) (h : α ^ N = 1)
    (hab : a ≡ b [MOD N]) : α ^ a = α ^ b := by
  rw [← Nat.div_add_mod a N, ← Nat.div_add_mod b N, pow_add, pow_add, pow_mul, pow_mul, h, one_pow,
    one_pow, hab]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem rootSum_eq_of_modEq (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X])
    (hf : f.Monic) (hi : Irreducible f) (hc : f.coeff 0 ≠ 0) (m k k' a : ℕ) (hd : f.natDegree ∣ m)
    (hk : k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1]) :
    rootSum θ k' f = rootSum θ k f := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  have hq : ringChar F ^ ((n : ℕ) * a) = Nat.card F ^ a := by
    rw [Nat.card_eq_fintype_card, hn, pow_mul]
  have hgal := GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F θ (RingHom.id F) ((n : ℕ) * a) (fun x => by
    rw [hq, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]; rfl) k f
  rw [Polynomial.map_id, hq] at hgal
  rw [hgal]
  unfold rootSum
  congr 1
  refine Multiset.map_congr rfl fun α hα => ?_
  have hf0 : f.map (algebraMap F (AlgebraicClosure F)) ≠ 0 := Polynomial.map_ne_zero hi.ne_zero
  have h0 : α ≠ 0 := by
    rintro rfl
    have h := (mem_roots hf0).1 hα
    rw [IsRoot, ← coeff_zero_eq_eval_zero, coeff_map] at h
    exact hc ((algebraMap F (AlgebraicClosure F)).injective (by rw [h, map_zero]))
  rw [← map_pow, ← map_pow,
    pow_eq_pow_of_modEq' α _ _ _ (pow_card_pow_sub_one_of_root F f hf hi m hd α hα h0) hk]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem cusp_eq_of_modEq : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ),
    (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ m k k' a : ℕ, 0 < m → k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1] →
      cusp θ m k' = cusp θ m k := by
  intro F _ _ θ _ m k k' a _ hk
  funext x
  unfold cusp psiG
  congr 1
  set V := Fin m → F
  set g : Module.End F V := Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)
  have hV : Finite V := Module.finite_of_finite F
  have hE : Finite (Module.End F V) := Finite.of_injective _ DFunLike.coe_injective
  have hs := (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one F θ k).1
  have hs' := (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one F θ k').1
  let φ : Module.End F V → ℂ := fun h => psi (rootSum θ k') V h - psi (rootSum θ k) V h
  have hc : IsClassFn φ := by
    intro e h
    simp only [φ, _root_.GlobalTheory.CuspGL.psi_conj]
  have hp : GlobalTheory.CuspGL.IsPrimitive φ := by
    intro A hA hA' g' hg'
    have e1 := _root_.GlobalTheory.CuspGL.isPrimitive_psi F V _ hs' A hA hA' g' hg'
    have e2 := _root_.GlobalTheory.CuspGL.isPrimitive_psi F V _ hs A hA hA' g' hg'
    have := finsum_mem_lin_comb_of_finite (nilRad A) 1 1 (fun h => psi (rootSum θ k') V (g' + h))
      (fun h => psi (rootSum θ k) V (g' + h))
    simp only [one_mul] at this
    simp only [φ]
    rw [this, e1, e2, sub_zero]
  have hP : (LinearMap.charpoly g).Monic := LinearMap.charpoly_monic g
  have hdeg : (LinearMap.charpoly g).natDegree = Module.finrank F V := LinearMap.charpoly_natDegree g
  have hdegm : (LinearMap.charpoly g).natDegree = m := by rw [hdeg, Module.finrank_fin_fun]
  have hc0 : (LinearMap.charpoly g).coeff 0 ≠ 0 := by
    intro h0
    have hdet := LinearMap.det_eq_sign_charpoly_coeff g
    rw [h0, mul_zero, LinearMap.det_toLin'] at hdet
    exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero hdet
  have hmang : mangoldt (rootSum θ k') (LinearMap.charpoly g) =
      mangoldt (rootSum θ k) (LinearMap.charpoly g) := by
    unfold mangoldt
    refine finsum_mem_congr rfl fun f hf => ?_
    obtain ⟨hfm, hfi, r, hr, hfr⟩ := hf
    refine rootSum_eq_of_modEq F θ f hfm hfi ?_ m k k' a ?_ hk
    · intro h
      apply hc0
      rw [hfr, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, h, zero_pow hr.ne']
    · refine ⟨r, ?_⟩
      rw [← hdegm, hfr, natDegree_pow, mul_comm]
  have hmass : mass φ (LinearMap.charpoly g) = 0 := by
    have := finsum_mem_lin_comb_of_finite {h : Module.End F V | LinearMap.charpoly h = LinearMap.charpoly g}
      1 1 (psi (rootSum θ k') V) (psi (rootSum θ k) V)
    simp only [one_mul] at this
    unfold mass
    simp only [φ]
    rw [this]
    have m1 := _root_.GlobalTheory.CuspGL.mass_psi_eq_glCard_mul_mangoldt_div F V _ hs' _ hP hdeg
    have m2 := _root_.GlobalTheory.CuspGL.mass_psi_eq_glCard_mul_mangoldt_div F V _ hs _ hP hdeg
    unfold mass at m1 m2
    rw [m1, m2, hmang, sub_self]
  exact sub_eq_zero.1 (GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero F V φ hc hp g hmass)

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegZeroCocycleExistsCoboundaryOfRichBased
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts.DegZero

theorem sub_rel {M : Type} [AddCommGroup M] {p0 p1 u0 u1 v0 v1 w z0 z1 : M}
    (c0 : p0 = u0 + w) (c0' : p0 = v0 + z0) (c1 : p1 = u1 + w) (c1' : p1 = v1 + z1) :
    u0 - u1 = v0 - v1 + (z0 - z1) := by
  have e0 : u0 = v0 + z0 - w := eq_sub_of_add_eq (c0.symm.trans c0')
  have e1 : u1 = v1 + z1 - w := eq_sub_of_add_eq (c1.symm.trans c1')
  rw [e0, e1]; abel

theorem sub_sub_eq_of_sub_eq_addCommGroup {M : Type} [AddCommGroup M] {h0 h1 j0 j1 d X : M}
    (e : h0 - h1 = d) (e' : j1 - j0 = d) : h0 - (X - j0) = h1 - (X - j1) := by
  have a0 : h0 = d + h1 := eq_add_of_sub_eq e
  have a1 : j1 = d + j0 := eq_add_of_sub_eq e'
  rw [a0, a1]; abel

theorem eq_inr {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
    (x : TrivSqZeroExt O M) (hx : x.fst = 0) : x = TrivSqZeroExt.inr x.snd :=
  TrivSqZeroExt.ext hx rfl

theorem tszeSec_sub_inl {g : ℕ} {O : Type} [CommRing O] [Algebra ℂ O] (D : Fin g → Derivation ℂ O O) (x : O) :
    tszeSec D x - TrivSqZeroExt.inl x = TrivSqZeroExt.inr fun a ↦ D a x := by
  show TrivSqZeroExt.inl x + TrivSqZeroExt.inr (fun a ↦ D a x) - TrivSqZeroExt.inl x = _
  abel

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}

theorem translationChartShiftSubstitution_comp_degZero {k k' k'' : K.K} (e : K.le 0 k' k) (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k)
    (f : Hol (K.W k)) : K.sh e' (K.sh e f) = K.sh e'' f :=
  Hol.ext_fn fun p hp ↦ by
    rw [fn_sh e' _ hp, fn_sh e _ (K.maps e' p hp), fn_sh e'' _ hp]
    simp only [F.shift_zero]

theorem ptHom_refl_triv (k : K.K) : ptHom (K.triv k) (K.le_refl k) = 𝟙 (K.triv k) :=
  hom_ext (fun c ↦ sh_refl (K.le_refl k) c) rfl

theorem ptHom_comp0 {k k' k'' : K.K} (e : K.le 0 k' k) (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k) :
    ptHom (K.triv k') e ≫ ptHom (K.triv k'') e' = ptHom (K.triv k'') e'' :=
  hom_ext (fun c ↦ translationChartShiftSubstitution_comp_degZero e e' e'' c) (add_zero (0 : Λ))

def corr (h : C1 K.Oc) (G : C0 K.Oc) : C1 K.Oc := fun T T' φ ↦ h T T' φ - (G T' - φ.φ (G T))

theorem zero_id (h : C1 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (T : K.Obj) : h T T (𝟙 T) = 0 := by
  have e := hc T T T (𝟙 T) (𝟙 T) rfl rfl
  rw [Category.id_comp] at e
  change (h T T (𝟙 T) : T.C) = h T T (𝟙 T) + h T T (𝟙 T) at e
  exact (add_eq_left.mp e.symm)

theorem corr_cocycle (h : C1 K.Oc) (G : C0 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) :
    ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      corr h G T T'' (φ ≫ ψ) = ψ.φ (corr h G T T' φ) + corr h G T' T'' ψ := by
  intro T T' T'' φ ψ hφ hψ
  change (h T T'' (φ ≫ ψ) : T''.C) - (G T'' - ψ.φ (φ.φ (G T))) =
    ψ.φ ((h T T' φ : T'.C) - (G T' - φ.φ (G T))) + ((h T' T'' ψ : T''.C) - (G T'' - ψ.φ (G T')))
  rw [hc T T' T'' φ ψ hφ hψ, map_sub, map_sub]
  abel

theorem vanish (h : C1 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ)
    (v1 : ∀ T : K.Obj, h _ _ (ptHom T (K.le_refl T.k)) = 0)
    (v2 : ∀ k k' (e : K.le 0 k' k), h _ _ (ptHom (K.triv k') e) = 0)
    (v3 : ∀ k, h _ _ (jet0 k) = h _ _ (jet1 k)) (T T' : K.Obj) (φ : T ⟶ T') (hφ : φ.deg = 0) :
    h T T' φ = 0 := by
  have hm := GlobalTheory.T.cochain_eq_of_same_degree_chartMorphism K h 0 (fun k T χ hχ ↦ by
    rw [hc _ _ _ (jet0 k) χ rfl hχ, hc _ _ _ (jet1 k) χ rfl hχ, v3 k])
  have v5 : ∀ (k : K.K) (T : K.Obj) (f : K.triv k ⟶ T), f.deg = 0 → h _ _ f = 0 := by
    intro k T f hd
    have e : K.le 0 T.k k := hd ▸ Charts.Hom.le f
    have hs : ∀ c : Hol (K.W k), K.sh (Charts.Hom.le f) c = K.sh (K.le_refl T.k) (K.sh e c) := fun c ↦ by
      rw [sh_refl]
      exact Hol.ext_fn fun p hp ↦ by rw [fn_sh (Charts.Hom.le f) c hp, fn_sh e c hp, hd]
    have hcomp : ptHom T (Charts.Hom.le f) = ptHom (K.triv T.k) e ≫ ptHom T (K.le_refl T.k) :=
      hom_ext (fun c ↦ congrArg T.ρ (hs c)) (hd.trans (add_zero (0 : Λ)).symm)
    rw [hm k T f hd, hcomp, hc _ _ _ _ _ rfl rfl, v2, v1, map_zero, add_zero]
  have e := hc _ _ _ (ptHom T (K.le_refl T.k)) φ rfl hφ
  rw [v5 _ _ _ ((zero_add φ.deg).trans hφ), v1, map_zero, zero_add] at e
  exact e.symm

def jetDiff (h : C1 K.Oc) (k : K.K) : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) :=
  h _ _ (jet0 k) - h _ _ (jet1 k)

def trans0 (h : C1 K.Oc) (k k' : K.K) (e : K.le 0 k' k) : Hol (K.W k') := h _ _ (ptHom (K.triv k') e)

theorem jetDiff_sh (h : C1 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (k k' : K.K) (e : K.le 0 k' k) (i : Fin g) :
    (jetDiff h k').snd i - K.sh e ((jetDiff h k).snd i) = dw i (trans0 h k k' e) := by
  obtain ⟨χ, hχ, h0, h1, hx⟩ := GlobalTheory.T.exists_jet_morphism_extending_translation K e
  have c0 := hc _ _ _ (jet0 k) χ rfl hχ
  have c1 := hc _ _ _ (jet1 k) χ rfl hχ
  rw [h0] at c0
  rw [h1] at c1
  have key := sub_rel c0 (hc _ _ _ (ptHom (K.triv k') e) (jet0 k') rfl rfl) c1
    (hc _ _ _ (ptHom (K.triv k') e) (jet1 k') rfl rfl)
  have key' : χ.φ (jetDiff h k) = (jet0 k').φ (trans0 h k k' e) - (jet1 k').φ (trans0 h k k' e) + jetDiff h k' :=
    (map_sub χ.φ _ _).trans key
  have s := (hx (jetDiff h k)).2 i
  rw [key'] at s
  have s' : (0 : Hol (K.W k')) - (tszeSec (g := g) dw (trans0 h k k' e)).snd i + (jetDiff h k').snd i =
      K.sh e ((jetDiff h k).snd i) := s
  rw [snd_tszeSec] at s'
  rw [← s']
  abel

def gauge (h : C1 K.Oc) (G₀ : ∀ k, Hol (K.W k)) : C0 K.Oc :=
  fun T ↦ (T.ρ (G₀ T.k) + (h _ _ (ptHom T (K.le_refl T.k)) : T.C) : T.C)

theorem exists_gauge : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∃ G : C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → h T T' φ = G T' - φ.φ (G T) := by
  intro I _ g Λ _ F K hR hB h hc
  have hcl := fun k ↦ _root_.GlobalTheory.AnPer.ClosedSq.connForm_closed K h hc k (jetDiff h k) rfl
  obtain ⟨G₀, hd, ha⟩ := GlobalTheory.T.exists_primitive_cech_poincare_rich_charts K hR hB (trans0 h) (fun k ↦ (jetDiff h k).snd)
    (fun k k' k'' e e' e'' ↦ by
      have c := hc _ _ _ (ptHom (K.triv k') e) (ptHom (K.triv k'') e') rfl rfl
      rw [ptHom_comp0 e e' e''] at c
      exact c)
    (fun k i j ↦ (hcl k).2 i j) (jetDiff_sh h hc)
  have gt : ∀ k, gauge h G₀ (K.triv k) = G₀ k := fun k ↦ by
    have z : h _ _ (ptHom (K.triv k) (K.le_refl k)) = 0 := by
      rw [ptHom_refl_triv]; exact zero_id h hc _
    exact (congrArg (fun x : Hol (K.W k) ↦ G₀ k + x) z).trans (add_zero _)
  refine ⟨gauge h G₀, fun T T' φ hφ ↦ sub_eq_zero.mp
    (vanish (corr h (gauge h G₀)) (corr_cocycle h _ hc) (fun T ↦ ?_) (fun k k' e ↦ ?_) (fun k ↦ ?_) T T' φ hφ)⟩
  · have z : (ptHom T (K.le_refl T.k)).φ (gauge h G₀ (K.triv T.k)) = T.ρ (G₀ T.k) := by
      rw [gt]; exact congrArg T.ρ (sh_refl (K.le_refl T.k) _)
    unfold corr
    rw [z]
    exact sub_eq_zero.mpr (add_sub_cancel_left (G := T.C) _ _).symm
  · unfold corr
    rw [gt, gt]
    exact sub_eq_zero.mpr (ha k k' e)
  · unfold corr
    rw [gt]
    refine sub_sub_eq_of_sub_eq_addCommGroup (d := TrivSqZeroExt.inr (jetDiff h k).snd) (eq_inr (jetDiff h k) (hcl k).1) ?_
    have z0 : (jet0 k).φ (G₀ k) = TrivSqZeroExt.inl (G₀ k) :=
      congrArg TrivSqZeroExt.inl (sh_refl (K.le_refl k) (G₀ k))
    rw [z0]
    exact (tszeSec_sub_inl dw (G₀ k)).trans (congrArg TrivSqZeroExt.inr (funext (hd k)))

end GlobalTheory.AnPer.Charts.DegZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DlogBasisAndVanishingAboveDimensionStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dlog_basis_and_vanishing_above_dimension : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → (∃ b : Module.Basis (Fin d) K Ω[K⁄k], ∀ j, b j = (algebraMap F K (x j.succ / x 0))⁻¹ • D k K (algebraMap F K (x j.succ / x 0))) ∧ ∀ q, d < q → ∀ y ∈ ⋀[K]^q Ω[K⁄k], y = 0 := by
  first | (exact @GlobalTheory.PD.IsFinCover.dlog_basis_and_vanish) | (exact GlobalTheory.PD.IsFinCover.dlog_basis_and_vanish) | (intros; apply GlobalTheory.PD.IsFinCover.dlog_basis_and_vanish <;> assumption)
end

