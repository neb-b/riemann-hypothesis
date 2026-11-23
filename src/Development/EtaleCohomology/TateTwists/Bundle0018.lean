module

public import Development.EtaleCohomology.TateTwists.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0012
public import Development.EtaleCohomology.TateTwists.Bundle0013

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSimplicialSchemeCocycleVanishingAtIdIsCobou
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma cob_altsum (k : ℕ) : ∑ i : Fin k, (-1 : ℤ) ^ (i : ℕ) = if k % 2 = 0 then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have : (j + j) % 2 = 0 := by omega
      have h2 : (j + j + 1) % 2 ≠ 0 := by omega
      simp [this, h2, ← two_mul, pow_mul]
    · have : (2 * j + 1) % 2 ≠ 0 := by omega
      have h2 : (2 * j + 1 + 1) % 2 = 0 := by omega
      simp [this, h2, pow_succ, pow_mul]

lemma cob_map_zsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℤ) (z : Sec F U) :
    Sec.map φ (c • z) = c • Sec.map φ z := by
  simp [Sec.map]

lemma cob_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := by
  simp [Sec.map]

lemma cob_res_zsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℤ) (z : Sec F U) :
    Sec.res g (c • z) = c • Sec.res g z := by
  simp [Sec.res]

end LateralTheory.EtaleFoundations

namespace LateralTheory.EtaleFoundations

noncomputable def cobB {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n : ℤ) (hmn : m + 1 = n)
    (α : Cochain ((chains R).obj (sch.obj X)) I n) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + m = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U :=
  fun p s h U x => if p % 2 = 1 then ((n.negOnePow : ℤ)) • ev α (p + 1) s (by push_cast; omega) U
    (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)) else 0

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etaleSimplicialScheme_cocycle_vanishing_at_id_isCoboundary_of_evaluati (hmk : EtaleSimplicialCochainExistsFromNaturalSections) (hdl : EtaleSimplicialCochainEvaluationDifferentialFormula)
    (hb : EtaleSimplicialCochainEvaluationProperties) : EtaleSimplicialSchemeCocycleVanishingAtIdIsCoboundary := by
  intro R _ X I m n hmn α h0
  have hεε : (n.negOnePow : ℤ) * (n.negOnePow : ℤ) = 1 := by
    rw [← Units.val_mul, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul]; rfl

  have hnat : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
      Sec.res g (cobB X I m n hmn α.1 p s h U x) = cobB X I m n hmn α.1 p s h V (x.res g) := by
    intro p s h V U g x
    unfold cobB
    split_ifs
    · rw [cob_res_zsmul]
      exact congrArg (((n.negOnePow : ℤ)) • ·) ((hb R).2.1 α.1 (p + 1) s _ V U g (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)))
    · simp [Sec.res]
  obtain ⟨β, hβ⟩ := hmk R (cobB X I m n hmn α.1) hnat
  refine ⟨β, ?_⟩

  have hα0 : ∀ U (x : Sx (sch.obj X) 0 U), ev α.1 0 n (by simp) U x = 0 := by
    intro U x
    have e : ev α.1 0 n (by simp) U x = Sec.res (x : U ⟶ X) (ev α.1 0 n (by simp) X (𝟙 X)) := by
      rw [(hb R).2.1 α.1 0 n (by simp) U X x (𝟙 X)]; rfl
    rw [e, h0]; simp [Sec.res]

  have hcyc : ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 2 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + n = t) U
      (x : Sx (sch.obj X) (p + 2) U), p % 2 = 0 →
      Sec.map (I.d s t) (ev α.1 (p + 2) s hs U x) = (n.negOnePow : ℤ) • ev α.1 (p + 1) t ht U
        (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)) := by
    intro p s t hs ht U x hp
    have e := (hdl R rfl α.1 U).2 (p + 1) s t hs (by push_cast at ht ⊢; omega) x
    rw [Cocycle.δ_eq_zero, ((hb R (E := sch.obj X) (I := I) (n := n + 1)).1 0 0 (p + 1 + 1) t _ U x).2.2.1] at e
    have hsum : ∑ i : Fin (p + 1 + 2), (-1 : ℤ) ^ (i : ℕ) • ev α.1 (p + 1) t (by push_cast at ht ⊢; omega) U (x.face i)
        = (∑ i : Fin (p + 1 + 2), (-1 : ℤ) ^ (i : ℕ)) • ev α.1 (p + 1) t ht U
          (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)) := by
      rw [Finset.sum_smul]; rfl
    rw [hsum, cob_altsum, if_neg (by omega), one_smul, Int.negOnePow_succ, Units.smul_def] at e
    rw [eq_comm, add_eq_zero_iff_eq_neg] at e
    rw [e]; simp
  apply (hb R).2.2.1
  intro p s h U x
  cases p with
  | zero =>
    obtain rfl : s = n := by omega
    rw [(hdl R hmn β U).1 x, hβ, hα0]
    simp [cobB, cob_map_zero]
  | succ p =>
    rw [(hdl R hmn β U).2 p (-((p + 1 : ℕ) : ℤ) + m) s rfl h x]
    simp only [hβ]
    have hsum : ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • cobB X I m n hmn α.1 p s (by push_cast at h ⊢; omega) U (x.face i)
        = (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ)) • cobB X I m n hmn α.1 p s (by push_cast at h ⊢; omega) U
          (show Sx (sch.obj X) p U from (x : U ⟶ X)) := by
      rw [Finset.sum_smul]; rfl
    rw [hsum, cob_altsum, Units.smul_def]
    rcases Nat.even_or_odd p with ⟨j, rfl⟩ | ⟨j, rfl⟩
    ·
      have h1 : (j + j + 1) % 2 = 1 := by omega
      have h2 : (j + j + 2) % 2 = 0 := by omega
      simp only [cobB, h1, h2, ↓reduceIte, zero_smul, smul_zero, add_zero]
      rw [cob_map_zsmul]
      have hc := hcyc (j + j) (-((j + j + 1 : ℕ) : ℤ) + m) s (by push_cast; omega) (by push_cast at h ⊢; omega) U x (by omega)
      erw [hc]
      rw [smul_smul, hεε, one_smul]
    · have h1 : (2 * j + 1 + 1) % 2 = 0 := by omega
      have h2 : (2 * j + 1 + 2) % 2 = 1 := by omega
      have h3 : (2 * j + 1) % 2 = 1 := by omega
      simp only [cobB, h1, h2, h3, ↓reduceIte, one_ne_zero, one_smul, smul_smul]
      rw [if_neg (by omega), cob_map_zero, zero_add, one_mul, hεε, one_smul]
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistMultiplicationGeneratorMapOfSectio
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations.TwMulGenMap

def twSec : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ

theorem nsmul_congr {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (n m : ℕ)
    (h : (n : ZMod q) = m) (x : M) : n • x = m • x := by
  have hn : (n : ULift.{1} (ZMod q)) = ULift.up (n : ZMod q) := by ext; simp
  have hm : (m : ULift.{1} (ZMod q)) = ULift.up (m : ZMod q) := by ext; simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), hn, hm, h]

theorem val_mul {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (i j k : ℤ) (hk : i + j = k) :
    ((((a ^ i : (ZMod q)ˣ) : ZMod q).val * ((a ^ j : (ZMod q)ˣ) : ZMod q).val : ℕ) : ZMod q) =
      ((((a ^ k : (ZMod q)ˣ) : ZMod q).val : ℕ) : ZMod q) := by
  rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← Units.val_mul,
    ← zpow_add, hk]

theorem sec_map_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℕ)
    (x : Sec F U) : Sec.map φ (n • x) = n • Sec.map φ x := map_nsmul _ _ _

open LateralTheory.EtaleFoundations.TwMulPf in
theorem genMap_of (h : twSec) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists := by
  intro q _ i j k T μ _ hk
  let π : (sgl T).X 0 ⟶ T := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 T).hom
  have hπ : π ≫ sglι T = 𝟙 _ := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 T).hom_inv_id
  let e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec T U := fun U ζ =>
    Sec.map π (μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)))
  have hnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    simp only [e]
    rw [sec_res_map, μ.nat, sec_res_map, sec_res_map, (h q i).2.2.2.1, (h q j).2.2.2.1]
  have hrel : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      e U ξ = ((a ^ k : (ZMod q)ˣ) : ZMod q).val • e U ζ := by
    intro U ζ ξ a hξ
    simp only [e]
    rw [(h q i).2.2.2.2.1 U ζ ξ a hξ, (h q j).2.2.2.2.1 U ζ ξ a hξ]
    rw [sec_map_nsmul, sec_map_nsmul, map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul,
      sec_map_nsmul, mul_comm, nsmul_congr _ _ (val_mul a i j k hk)]
  obtain ⟨φ, hφ, -⟩ := (h q k).2.2.2.2.2 T e hnat hrel
  refine ⟨φ, fun U ζ => ?_⟩
  rw [hφ U ζ]
  simp only [e]
  rw [sec_map_comp, hπ, sec_map_id]

end LateralTheory.EtaleFoundations.TwMulGenMap

theorem LateralTheory.EtaleFoundations.etale_tate_twist_multiplication_generator_map_of_section_description (h : LateralTheory.EtaleFoundations.TwMulGenMap.twSec) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists :=
  LateralTheory.EtaleFoundations.TwMulGenMap.genMap_of h
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistMultiplicationTensorExistsOfComple
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations.TensExPf
open LateralTheory.EtaleFoundations.TwMulPf
open scoped TensorProduct DirectSum

variable {R : Type} [CommRing R]

theorem sec_map_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := by
  rfl

theorem sec_zero_of_isZero {Z : Shv R} (hZ : IsZero Z) {U : Scheme.{0}} (y : Sec Z U) : y = 0 := by
  have h : Sec.map (𝟙 Z) y = Sec.map 0 y := by rw [hZ.eq_of_src (𝟙 Z) 0]
  rw [sec_map_id, sec_map_zero] at h
  exact h

theorem isZero_sglX (F : Shv R) {w : ℤ} (hw : w ≠ 0) : IsZero ((sgl F).X w) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ hw

theorem sgl_d (F : Shv R) (a : ℤ) : (sgl F).d a (a + 1) = 0 := by
  by_cases ha : a = 0
  · exact (isZero_sglX F (by omega)).eq_of_tgt _ _
  · exact (isZero_sglX F ha).eq_of_src _ _

def eIso (K : Cx R) (w : ℤ) (h : w = 0) : K.X w ≅ (sgl (K.X 0)).X w :=
  K.XIsoOfEq h ≪≫ (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (K.X 0) w h).symm

def e (K : Cx R) (w : ℤ) : K.X w ⟶ (sgl (K.X 0)).X w :=
  if h : w = 0 then (eIso K w h).hom else 0

theorem e_pos (K : Cx R) {w : ℤ} (h : w = 0) : e K w = (eIso K w h).hom := dif_pos h

def μ {A B : Shv R} {K : Cx R} (τ : Pair (sgl A) (sgl B) K) : Pair (sgl A) (sgl B) (sgl (K.X 0)) where
  mul U s t w h := (τ.mul U s t w h).compr₂ (secL (e K w) U)
  nat g s t w h a b := by
    change Sec.res g (Sec.map (e K w) _) = Sec.map (e K w) _
    rw [sec_res_map, τ.nat]
  leibniz U s t w h a b := by
    change Sec.map ((sgl (K.X 0)).d w (w + 1)) _ =
      Sec.map (e K (w + 1)) (τ.mul U (s + 1) t (w + 1) _ (Sec.map ((sgl A).d s (s + 1)) a) b) +
        s.negOnePow • Sec.map (e K (w + 1)) (τ.mul U s (t + 1) (w + 1) _ a (Sec.map ((sgl B).d t (t + 1)) b))
    simp only [sgl_d, sec_map_zero, map_zero, LinearMap.zero_apply, smul_zero, add_zero]

theorem μ_lift {A B : Shv R} {K : Cx R} (τ : Pair (sgl A) (sgl B) K) (U : Scheme.{0}) (w : ℤ)
    (x : Tens (sgl A) (sgl B) U w) : (μ τ).lift U w x = Sec.map (e K w) (τ.lift U w x) := by
  classical
  change _ = secL (e K w) U (τ.lift U w x)
  rw [← LinearMap.comp_apply]
  congr 1
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp [Pair.lift, μ]

theorem tens_summand_zero {A B : Shv R} {a b : ℤ} (hab : a ≠ 0 ∨ b ≠ 0) {U : Scheme.{0}}
    (z : Sec ((sgl A).X a) U ⊗[ULift.{1} R] Sec ((sgl B).X b) U) : z = 0 := by
  refine TensorProduct.induction_on (motive := fun z => z = 0) z rfl (fun u v => ?_) (fun x y hx hy => by rw [hx, hy, add_zero])
  rcases hab with h | h
  · rw [sec_zero_of_isZero (isZero_sglX A h) u, TensorProduct.zero_tmul]
  · rw [sec_zero_of_isZero (isZero_sglX B h) v, TensorProduct.tmul_zero]

theorem tens_zero {A B : Shv R} {U : Scheme.{0}} {w : ℤ} (hw : w ≠ 0) (x : Tens (sgl A) (sgl B) U w) : x = 0 := by
  refine DirectSum.ext fun p => ?_
  rw [DirectSum.zero_apply]
  refine tens_summand_zero ?_ _
  have := p.2
  by_contra hc
  push Not at hc
  omega

theorem μ_isTensor {A B : Shv R} {K : Cx R} (τ : Pair (sgl A) (sgl B) K) (hτ : τ.IsTensor) :
    (μ τ).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · by_cases hw : w = 0
    · refine loc_mono (hτ.1 U w (Sec.map (eIso K w hw).inv y)) fun V g ⟨x, hx⟩ => ⟨x, ?_⟩
      rw [μ_lift, hx, ← sec_res_map, e_pos K hw, sec_map_comp, Iso.inv_hom_id, sec_map_id]
    · refine ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => ⟨0, ?_⟩⟩
      rw [map_zero]
      exact (sec_zero_of_isZero (isZero_sglX _ hw) _).symm
  · by_cases hw : w = 0
    · refine hτ.2 U w x ?_
      rw [μ_lift, e_pos K hw] at hx
      have := congrArg (Sec.map (eIso K w hw).inv) hx
      rw [sec_map_comp, Iso.hom_inv_id, sec_map_id] at this
      rw [this]
      exact map_zero _
    · obtain rfl := tens_zero hw x
      exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => map_zero _⟩

end LateralTheory.EtaleFoundations.TensExPf

open LateralTheory.EtaleFoundations.TensExPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_multiplication_tensor_exists_of_complex_tensor_exists
    (hex : ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor) :
    LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists := by
  intro q _ i j
  obtain ⟨K, τ, hτ⟩ := hex (ZMod q) (sgl (tw q i)) (sgl (tw q j))
  exact ⟨K.X 0, μ τ, μ_isTensor τ hτ⟩
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorComplexLocallyExactOfLiftedSections
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem stair_loc_bind (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  classical
  obtain ⟨S, hS, hSP⟩ := hP
  refine ⟨Sieve.bind S.arrows (fun V g hg => Classical.choose (h V g (hSP V g hg))), ?_, ?_⟩
  · exact (Scheme.etaleTopology).bind_covering hS (fun V g hg => (Classical.choose_spec (h V g (hSP V g hg))).1)
  · rintro W f ⟨V, k, g, hg, hk, rfl⟩
    exact (Classical.choose_spec (h V g (hSP V g hg))).2 W k hk

theorem stair_loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

theorem stair_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.map φ (Sec.res g y) = Sec.res g (Sec.map φ y) := by
  have := congrArg (fun m => (ModuleCat.Hom.hom m) y) (φ.hom.naturality g.op)
  simpa using this.symm

theorem stair_res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res k (Sec.res g y) = Sec.res (k ≫ g) y := by
  simp [Sec.res]

def EtaleTensorCyclesLocallyLiftOfFlatBounded : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) →
    (∀ (s : ℤ) (U : Scheme.{0}) (y : Sec (C.sc s).X₂ U), Sec.map (C.sc s).g y = 0 →
      Loc U fun V g => ∃ x : Sec (C.sc s).X₁ V, Sec.map (C.sc s).f x = Sec.res g y) →
    ∀ (w : ℤ) (U : Scheme.{0}) (x : Tens C J U w), Sec.map (T.sc w).g (τ.lift U w x) = 0 →
      Loc U fun V g => ∃ z : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f z = Sec.res g (τ.lift U w x)

theorem etale_tensor_complex_locally_exact_of_lifted_sections (hL : EtaleTensorCyclesLocallyLiftOfFlatBounded) : EtaleTensorComplexLocallyExactOfFlatBounded := by
  intro R _ C J T a b _ _ τ hτ hJ hC w U y hy
  refine stair_loc_bind U _ _ (hτ.1 U w y) ?_
  rintro V g ⟨x, hx⟩
  have hcyc : Sec.map (T.sc w).g (τ.lift V w x) = 0 := by
    have h1 := stair_map_res (T.sc w).g g y
    have h2 : Sec.map (T.sc w).g (τ.lift V w x) = Sec.map (T.sc w).g (Sec.res g y) := congrArg _ hx
    refine h2.trans (h1.trans ?_)
    rw [hy]
    simp
  refine stair_loc_mono V _ _ (hL R a b τ hτ hJ hC w V x hcyc) ?_
  rintro W k ⟨z, hz⟩
  refine ⟨z, ?_⟩
  exact hz.trans ((congrArg (Sec.res k) hx).trans (stair_res_res k g y))

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorPairingDegreewiseUniversalOfSheafific
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations.TensUnivDeg

variable {R : Type} [CommRing R]

theorem tens_ind {I J : Cx R} (V : Scheme.{0}) (w : ℤ) (P : Tens I J V w → Prop) (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b))
    (hm : ∀ (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) V) (b : Sec (J.X p.1.2) V),
      P (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V)) p (a ⊗ₜ b)))
    (x : Tens I J V w) : P x := by
  classical
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | of p t =>
    rw [← DirectSum.lof_eq_of (ULift.{1} R)]
    induction t using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => exact hm p a b
    | add a b ha hb => rw [map_add (f := _)]; exact hadd _ _ ha hb
  | add a b ha hb => exact hadd _ _ ha hb

theorem res_lof {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V)) p (Sec.res g a ⊗ₜ Sec.res g b) := by
  classical
  simp [Tens.res, Sec.res]

theorem lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) p (a ⊗ₜ b)) = μ.mul U p.1.1 p.1.2 w p.2 a b := by
  classical
  simp [Pair.lift]

def Tmap {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →ₗ[ULift.{1} R] Tens I' J' U w :=
  DirectSum.lmap fun p => TensorProduct.map ((f.f p.1.1).hom.app (op U)).hom ((g.f p.1.2).hom.app (op U)).hom

theorem tmap_lof {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tmap f g U w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I'.X p.1.1) U ⊗[ULift.{1} R] Sec (J'.X p.1.2) U)) p (Sec.map (f.f p.1.1) a ⊗ₜ Sec.map (g.f p.1.2) b) := by
  classical
  simp [Tmap, Sec.map]

def TP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind U.unop w (fun x => Tens.res (𝟙 U.unop) w x = x) (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · rw [map_add (f := _), ha, hb]
    · rw [res_lof]; simp [Sec.res]
  map_comp g h := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind _ w (fun x => Tens.res (g ≫ h).unop w x = Tens.res h.unop w (Tens.res g.unop w x))
      (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · rw [map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
    · rw [res_lof, res_lof, res_lof]; simp [Sec.res]

def alpha {I J K : Cx R} (τ : Pair I J K) (w : ℤ) : TP I J w ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (τ.lift U.unop w)
  naturality U V g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind U.unop w (fun x => τ.lift V.unop w (Tens.res g.unop w x) = Sec.res g.unop (τ.lift U.unop w x))
      (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · simp only [map_add (f := _), ha, hb]
    · rw [res_lof, lift_lof, lift_lof, τ.nat]

def beta {I J I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ) : TP I J w ⟶ (K'.X w).obj where
  app U := ModuleCat.ofHom (ν.lift U.unop w ∘ₗ Tmap f g U.unop w)
  naturality U V e := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind U.unop w (fun x => ν.lift V.unop w (Tmap f g V.unop w (Tens.res e.unop w x)) =
        Sec.res e.unop (ν.lift U.unop w (Tmap f g U.unop w x)))
      (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · simp only [map_add (f := _), ha, hb]
    · rw [res_lof, tmap_lof, tmap_lof, lift_lof, lift_lof, ν.nat, TensUnivPf.nat_sec, TensUnivPf.nat_sec]

theorem alpha_locSurj {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology (alpha τ w) where
  imageSieve_mem {U} y := by
    obtain ⟨S, hS, hh⟩ := hτ.1 U w y
    refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) hS
    obtain ⟨x, hx⟩ := hh V g hg
    exact ⟨x, hx⟩

theorem etale_tensor_pairing_lift_eq_locally_res_eq {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) {U : Scheme.{0}}
    (x y : Tens I J U w) (h : τ.lift U w x = τ.lift U w y) :
    Loc U fun _ g => Tens.res g w x = Tens.res g w y := by
  obtain ⟨S, hS, hh⟩ := hτ.2 U w (x - y) (by rw [map_sub, h, sub_self])
  exact ⟨S, hS, fun V g hg => sub_eq_zero.1 (by rw [← map_sub]; exact hh V g hg)⟩

theorem alpha_locInj {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallyInjective Scheme.etaleTopology (alpha τ w) where
  equalizerSieve_mem {U} x y h := by
    obtain ⟨S, hS, hh⟩ := etale_tensor_pairing_lift_eq_locally_res_eq τ hτ w x y h
    exact Scheme.etaleTopology.superset_covering (fun V g hg => hh V g hg) hS

end LateralTheory.EtaleFoundations.TensUnivDeg

open LateralTheory.EtaleFoundations.TensUnivDeg in
theorem LateralTheory.EtaleFoundations.etale_tensor_pairing_degreewise_universal_of_sheafification : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists := by
  intro R _ I J K τ hτ I' J' K' ν f g w
  have := alpha_locSurj τ hτ w
  have := alpha_locInj τ hτ w
  have hW : Scheme.etaleTopology.W (alpha τ w) := GrothendieckTopology.W_of_isLocallyBijective _ _
  obtain ⟨m, hm⟩ := (hW (K'.X w).obj (K'.X w).property).2 (beta ν f g w)
  refine ⟨⟨m⟩, fun U s t h a b => ?_⟩
  have e := congrArg (fun φ : TP I J w ⟶ (K'.X w).obj => (φ.app (op U)).hom
    (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) ⟨(s, t), h⟩ (a ⊗ₜ b))) hm
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e
  change Sec.map ⟨m⟩ (τ.lift U w _) = (ν.lift U w ∘ₗ Tmap f g U w) _ at e
  rw [lift_lof, LinearMap.comp_apply, tmap_lof, lift_lof] at e
  exact e
end

-- bundled from Development.EtaleCohomology.TateTwists.TtTensGePf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tens_univ_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0)

theorem tt_tens_ge_of (h : tens_univ_ge) : tt_tens_ge := by
  intro R _ I J K μ hI hJ hμ
  exact h R μ hμ hI hJ

end LateralTheory.EtaleFoundations
end

