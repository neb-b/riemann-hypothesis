module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSequenceEtaleTateTwist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductShintaniLiftGalois
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem deg_of_forall₂ {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) {L₁ L₂ : List (ℕ × ℕ)}
    (h : List.Forall₂ (fun p p' : ℕ × ℕ => p.1 = p'.1 ∧ cusp θ p.1 p.2 = cusp θ p.1 p'.2) L₁ L₂) :
    deg L₁ = deg L₂ := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    simp only [deg, List.map_cons, List.sum_cons] at ih ⊢
    rw [hab.1, ih]

theorem J_congr_forall₂ {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) {L₁ L₂ : List (ℕ × ℕ)}
    (h : List.Forall₂ (fun p p' : ℕ × ℕ => p.1 = p'.1 ∧ cusp θ p.1 p.2 = cusp θ p.1 p'.2) L₁ L₂) :
    J θ L₁ = J θ L₂ := by
  induction h with
  | nil => rfl
  | @cons a b l₁ l₂ hab hl ih =>
    funext n
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    obtain ⟨h1, h2⟩ := hab
    simp only at h1 h2
    subst h1
    rw [J_cons, J_cons, ih, deg_of_forall₂ θ hl]
    simp only [h2]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem forall₂_flatMap_of {α β : Type} (R : β → β → Prop) (L : List α) (f g : α → List β)
    (h : ∀ p ∈ L, List.Forall₂ R (f p) (g p)) : List.Forall₂ R (L.flatMap f) (L.flatMap g) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.flatMap_cons]
    exact List.rel_append (h a (by simp)) (ih fun p hp => h p (by simp [hp]))

theorem cusp_mul_card_pow (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (θ : AlgebraicClosure F' →* ℂ) (m K : ℕ) :
    cusp θ m (K * Nat.card F ^ Module.finrank F F') = cusp θ m K := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite F'
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨r, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
  have hq : Nat.card F = ringChar F' ^ (r : ℕ) := by rw [Nat.card_eq_fintype_card, hcard, hchar]
  funext x
  have key := GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F' θ (RingEquiv.refl F') (r * Module.finrank F F') (fun y => by
    rw [pow_mul, ← hq, Nat.card_eq_fintype_card, ← Module.card_eq_pow_finrank, FiniteField.pow_card]
    rfl) m K x
  rw [hq, ← pow_mul, ← key]
  congr 1

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem J_liftL_galAct_frob (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (θ : AlgebraicClosure F' →* ℂ) [Fintype F] (L : List (ℕ × ℕ)) (n : ℕ)
    (hn : n = deg (liftL (Nat.card F) (Module.finrank F F') L)) (x : GL (Fin n) F') :
    J θ (liftL (Nat.card F) (Module.finrank F F') L) n
      (galAct F F' n (FiniteField.frobeniusAlgEquivOfAlgebraic F F') x) =
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n x := by
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨r, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
  have hq : Nat.card F = ringChar F' ^ (r : ℕ) := by rw [Nat.card_eq_fintype_card, hcard, hchar]
  set q := Nat.card F with hqdef
  set l := Module.finrank F F' with hldef
  have hl : 0 < l := Module.finrank_pos
  obtain ⟨l', hl'⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have key := GlobalTheory.T.harishChandraProductCuspidalGL_frobenius_pow F' θ (FiniteField.frobeniusAlgEquivOfAlgebraic F F').toRingEquiv r (fun y => by
    rw [← hq]
    show (FiniteField.frobeniusAlgEquivOfAlgebraic F F') y = _
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hqdef, Nat.card_eq_fintype_card]) (liftL q l L) n x
  rw [galAct_apply]
  refine (key.trans ?_)
  rw [← hq]

  set R : List (ℕ × ℕ) := L.flatMap fun p =>
    (List.range l').map (fun i => (p.1 / l, p.2 * q ^ (i + 1))) ++ [(p.1 / l, p.2)] with hR
  have hF : List.Forall₂ (fun p p' : ℕ × ℕ => p.1 = p'.1 ∧ cusp θ p.1 p.2 = cusp θ p.1 p'.2)
      ((liftL q l L).map fun p => (p.1, p.2 * q)) R := by
    rw [liftL, List.map_flatMap, hR]
    apply forall₂_flatMap_of
    intro p _
    rw [hl', List.range_succ, List.map_append, List.map_append]
    simp only [List.map_map, List.map_cons, List.map_nil]
    refine List.rel_append ?_ ?_
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro z _
      refine ⟨rfl, ?_⟩
      simp only [Function.comp_apply, pow_succ, mul_assoc]
    · refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
      simp only [Function.comp_apply]
      rw [mul_assoc, ← pow_succ, ← hl']
      exact cusp_mul_card_pow F F' θ _ _
  have hP : R.Perm (liftL q l L) := by
    rw [liftL, hR]
    apply List.Perm.flatMap_left
    intro p _
    rw [hl', List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, pow_zero, mul_one]
    refine List.perm_append_comm.trans ?_
    simp [Function.comp_def, ← hl']
  have hdeg : deg R = deg (liftL q l L) := by
    unfold deg
    exact (hP.map Prod.fst).sum_eq
  rw [J_congr_forall₂ θ hF]
  exact ((GlobalTheory.T.harishChandraProductCuspidalGL_list_properties F' θ).2.2 R (liftL q l L) n (hn.trans hdeg.symm) hP) ▸ rfl

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem J_liftL_galAct : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (θ : AlgebraicClosure F' →* ℂ)
    (t : F' ≃ₐ[F] F') (L : List (ℕ × ℕ)) (n : ℕ), n = deg (liftL (Nat.card F) (Module.finrank F F') L) →
    ∀ x : GL (Fin n) F', J θ (liftL (Nat.card F) (Module.finrank F F') L) n (galAct F F' n t x) =
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n x := by
  intro F F' _ _ _ _ θ t L n hn
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  letI := Fintype.ofFinite F
  obtain ⟨i, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 t
  suffices h : ∀ k : ℕ, ∀ x : GL (Fin n) F',
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n
        (galAct F F' n (FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ k) x) =
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n x from h i.1
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, map_mul, MulAut.mul_apply, ih]
    exact J_liftL_galAct_frob F F' θ L n hn x

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveComplexMapQuasiIsoOfUnitSchemes
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.DiscSupp

theorem assemble : ∀ (R : Type) [CommRing R] {ι : Type} [Fintype ι] (L : ι → Cx R) (C : Cx R) (d : ι → ℤ) (ψ : ∀ j, Cocycle (L j) C (d j)) (m₀ : ℤ), (∀ j, (L j).IsStrictlyGE m₀) → (∀ j n, CategoryTheory.Injective ((L j).X n)) → ∃ (D : Cx R) (f : D ⟶ C) (m : ℤ), D.IsStrictlyGE m ∧ (∀ n, CategoryTheory.Injective (D.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : (∀ j, CohomologyClass K (L j) (n - d j)) ≃ CohomologyClass K D n, ∀ a, cpush K f n (e a) = ∑ j, cpost K (ψ j) (n - d j) n (by omega) (a j) := by
  intro R _ ι _ L C d ψ m₀ hL hLi
  choose L' g hb hi he using fun j => GlobalTheory.T.cocycle_eq_chainMap_shift_compat_classes R (L j) C (d j) (ψ j)
  choose e he using he
  have hm : ∀ j, (L' j).IsStrictlyGE (m₀ - ∑ k, |d k|) := fun j => by
    haveI := hb j m₀ (hL j)
    refine isStrictlyGE_of_ge (L' j) _ (m₀ + d j) ?_
    have h1 : |d j| ≤ ∑ k, |d k| := Finset.single_le_sum (f := fun k => |d k|) (fun k _ => abs_nonneg (d k)) (Finset.mem_univ j)
    have h2 := neg_abs_le (d j)
    omega
  obtain ⟨D, f, hD, hDi, hs⟩ := GlobalTheory.T.exists_biproduct_chainMap_of_injective_family R L' C g (m₀ - ∑ k, |d k|) hm (fun j => hi j (hLi j))
  refine ⟨D, f, _, hD, hDi, fun K n => ?_⟩
  obtain ⟨e', he'⟩ := hs K n
  refine ⟨(Equiv.piCongrRight fun j => e j K n).trans e', fun a => ?_⟩
  simp only [Equiv.trans_apply, Equiv.piCongrRight_apply, he']
  exact Finset.sum_congr rfl fun j _ => he j K n (a j)

theorem bijective_disc : ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] (L : ι → Cx (ZMod q)) (C : Cx (ZMod q)) (d : ι → ℤ) (ψ : ∀ j, Cocycle (L j) C (d j)) (m₀ : ℤ), (∀ j, (L j).IsStrictlyGE m₀) → C.IsStrictlyGE m₀ → (∀ j n, CategoryTheory.Injective ((L j).X n)) → (∀ n, CategoryTheory.Injective (C.X n)) → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (sch.obj U)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j)) → ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j) := by
  intro q _ ι _ L C d ψ m₀ hL hC hLi hCi hU F hF
  obtain ⟨D, f, m, hD, hDi, he⟩ := assemble (ZMod q) L C d ψ m₀ hL hLi
  have hD' : D.IsStrictlyGE (min m m₀) := isStrictlyGE_of_ge D _ _ (min_le_left _ _)
  have hC' : C.IsStrictlyGE (min m m₀) := isStrictlyGE_of_ge C _ _ (min_le_right _ _)
  obtain ⟨hKI, hcone⟩ := GlobalTheory.T.mappingCone_isKInjective_bijective_hypercohomology_iff (ZMod q) f (min m m₀) hD' hC' hDi hCi
  have key : ∀ K : Cx (ZMod q), (∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass K (L j) (n - d j) =>
      ∑ j, cpost K (ψ j) (n - d j) n (by omega) (a j)) ↔ ∀ n, Subsingleton (CohomologyClass K (mappingCone f) n) := by
    intro K
    rw [← hcone K]
    refine forall_congr' fun n => ?_
    obtain ⟨e, he'⟩ := he K n
    have : (fun a : ∀ j, CohomologyClass K (L j) (n - d j) => ∑ j, cpost K (ψ j) (n - d j) n (by omega) (a j)) =
        (cpush K f n) ∘ e := funext fun a => (he' a).symm
    rw [this]
    exact Function.Bijective.of_comp_iff _ e.bijective
  refine (key _).mpr ?_
  exact GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support (ZMod q) (disc.obj F) (mappingCone f) (fun U hU' n b hb =>
    GlobalTheory.T.sectionsComplex_exact_etaleLocally_of_no_classes (ZMod q) (mappingCone f) U ((key _).mp (hU U (hF U hU'))) n b hb)

end GlobalTheory.EtC.DiscSupp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveProjBundleModelCochainComplexX
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC
open CupSpec

variable {R : Type} [CommRing R]

section Build
variable (q N : ℕ) (I : Cx R) (n : ℤ) {B : Shv R}
  (χ : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ V : Scheme.{0}, Sx (fibQ q N) p V → Sec B V →ₗ[ULift.{1} R] Sec (I.X s) V)
  (hχ : ∀ p s h (V W : Scheme.{0}) (w : W ⟶ V) (x : Sx (fibQ q N) p V) (b : Sec B V),
      Sec.res w (χ p s h V x b) = χ p s h W (x.res w) (Sec.res w b))
include hχ in
theorem buildC_exists (U : Scheme.{0}) (b : Sec B U) :
    ∃ α : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n, ∀ p s h W y,
      _root_.GlobalTheory.EtC.ev (R := R) α p s h W y =
        χ p s h W (y.map prod.snd) (Sec.res (show W ⟶ U from y.map prod.fst) b) := by
  let E : Spc := sch.obj U ⨯ fibQ q N
  let a (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E p W) :=
    χ p s h W (y.map prod.snd) (Sec.res (show W ⟶ U from y.map prod.fst) b)
  have ha (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (V W : Scheme.{0})
      (g : V ⟶ W) (y : Sx E p W) : Sec.res g (a p s h W y) = a p s h V (y.res g) := by
    dsimp only [a]
    erw [hχ, secRes_res, sxMap_res, sxMap_res]
    rfl
  have components (i j : ℤ) (hij : i + n = j) :
      ∃ φ : ((chains R).obj E).X i ⟶ I.X j, ∀ (p : ℕ) (hp : i = -(p : ℤ)) W y,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ)
          (freeGen R _ W y) = a p j (hp ▸ hij) W y := by
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp W y => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ W y
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using components
  refine ⟨Cochain.mk φ, fun p s h W y => ?_⟩
  have he := hφ _ _ h p rfl W y
  rw [eqToHom_refl, Category.id_comp] at he
  exact he

def cochainOfSection (U : Scheme.{0}) (b : Sec B U) : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n :=
  (buildC_exists q N I n χ hχ U b).choose

theorem buildC_ev (U : Scheme.{0}) (b : Sec B U) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (W : Scheme.{0})
    (y : Sx (sch.obj U ⨯ fibQ q N) p W) :
    _root_.GlobalTheory.EtC.ev (R := R) (cochainOfSection q N I n χ hχ U b) p s h W y =
      χ p s h W (y.map prod.snd) (Sec.res (show W ⟶ U from y.map prod.fst) b) :=
  (buildC_exists q N I n χ hχ U b).choose_spec p s h W y

include χ hχ in
def buildMor : B.obj ⟶ cotPre R q N I n := by
  have evExt {E : Spc} (α β : Cochain ((chains R).obj E) I n)
      (he : ∀ p s h W y, ev (R := R) α p s h W y = ev (R := R) β p s h W y) : α = β := by
    ext i s h : 1
    by_cases hi : i ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E p).inv]
      exact free_ext _ _ (fun W y => he p s h W y)
    · exact (isZero_chains E i (by omega)).eq_of_src _ _
  have evAdd {E : Spc} (α β : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E p W) :
      ev (R := R) (α + β) p s h W y = ev (R := R) α p s h W y + ev (R := R) β p s h W y := by
    simp [ev, Cochain.add_v]
  have evSmul {E : Spc} (r : ULift.{1} R) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E p W) :
      ev (R := R) (r • α) p s h W y = r • ev (R := R) α p s h W y := by
    unfold ev
    rw [Cochain.smul_v, Linear.comp_smul]
    rfl
  refine
    { app := fun U => ModuleCat.ofHom
        { toFun := cochainOfSection q N I n χ hχ U.unop
          map_add' := fun b b' => evExt _ _ (fun p s h W y => by
            simp only [evAdd, buildC_ev, Sec.res, map_add])
          map_smul' := fun r b => evExt _ _ (fun p s h W y => by
            simp only [RingHom.id_apply, evSmul, buildC_ev, Sec.res, map_smul]) }
      naturality := ?_ }
  intro U U' g
  have evPull {E E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E' p W) :
      ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h W y =
        ev (R := R) α p s h W (y.map f) := by
    unfold ev
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ W y)) = _
    rw [freeGen_map]
    rfl
  ext b : 2
  refine evExt _ _ (fun p s h W y => ?_)
  change ev (R := R) (cochainOfSection q N I n χ hχ U'.unop (Sec.res g.unop b)) p s h W y =
    ev (R := R) (((cotPre R q N I n).map g.unop.op).hom (cochainOfSection q N I n χ hχ U.unop b)) p s h W y
  have e2 := evPull (prod.map (sch.map g.unop) (𝟙 (fibQ q N)))
    (cochainOfSection q N I n χ hχ U.unop b) p s h W y
  refine Eq.trans ?_ e2.symm
  let f := prod.map (sch.map g.unop) (𝟙 (fibQ q N))
  have hsnd : (y.map f).map prod.snd = y.map prod.snd := by
    rw [← sxMap_comp, prod.map_snd, Category.comp_id]
  have hfst : (show W ⟶ U.unop from (y.map f).map prod.fst) =
      (show W ⟶ U'.unop from y.map prod.fst) ≫ g.unop := by
    change (y.map f).map prod.fst = schSx ((show W ⟶ U'.unop from y.map prod.fst) ≫ g.unop) p
    rw [← sxMap_comp, prod.map_fst, sxMap_comp]
    exact schSx_map (show W ⟶ U'.unop from y.map prod.fst) g.unop p
  erw [buildC_ev, buildC_ev, secRes_res, hsnd, hfst]

end Build

theorem injective_cotSheaf (q N : ℕ) (I : Cx R) (hI : ∀ m, Injective (I.X m)) (n : ℤ)
    (hS : Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n)) :
    Injective (⟨cotPre R q N I n, hS⟩ : Shv R) := by
  constructor
  intro A B g f hf
  let eval {E : Spc} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (V : Scheme.{0}) (x : Sx E p V) :
      Cochain ((chains R).obj E) I n →ₗ[ULift.{1} R] Sec (I.X s) V :=
    { toFun := fun α => ev (R := R) α p s h V x
      map_add' := fun α β => by simp [ev, Cochain.add_v]
      map_smul' := fun r α => by
        unfold ev
        rw [Cochain.smul_v, Linear.comp_smul]
        rfl }
  have evRes {E : Spc} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
      {V W : Scheme.{0}} (w : W ⟶ V) (x : Sx E p V) :
      Sec.res w (ev (R := R) α p s h V x) = ev (R := R) α p s h W (x.res w) := by
    change Sec.res w (Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (freeGen R _ V x)) = _
    rw [map_res, freeGen_res]
    rfl
  have evPull {E E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E' p W) :
      ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h W y =
        ev (R := R) α p s h W (y.map f) := by
    unfold ev
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ W y)) = _
    rw [freeGen_map]
    rfl
  let ψ : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ V : Scheme.{0}, Sx (fibQ q N) p V → Sec A V →ₗ[ULift.{1} R] Sec (I.X s) V :=
    fun p s h V x => (eval p s h V (sxPair (schSx (𝟙 V) p) x)).comp (g.hom.app (op V)).hom
  have hψ : ∀ p s h (V W : Scheme.{0}) (w : W ⟶ V) (x : Sx (fibQ q N) p V) (a : Sec A V),
      Sec.res w (ψ p s h V x a) = ψ p s h W (x.res w) (Sec.res w a) := by
    intro p s h V W w x a
    have hn : (g.hom.app (op W)).hom (Sec.res w a) = ((cotPre R q N I n).map w.op).hom ((g.hom.app (op V)).hom a) :=
      ConcreteCategory.congr_hom (g.hom.naturality w.op) a
    refine (evRes (E := sch.obj V ⨯ fibQ q N)
      ((g.hom.app (op V)).hom a) p s h w _).trans ?_
    refine Eq.trans ?_ (congrArg (fun c => _root_.GlobalTheory.EtC.ev (R := R) (E := sch.obj W ⨯ fibQ q N) (I := I) c p s h W
      (sxPair (schSx (𝟙 W) p) (x.res w))) hn).symm
    have e2 := evPull (prod.map (sch.map w) (𝟙 (fibQ q N))) ((g.hom.app (op V)).hom a) p s h W
      (sxPair (schSx (𝟙 W) p) (x.res w))
    refine Eq.trans ?_ e2.symm
    rw [sxPair_res, sxPair_map]
    congr 2
  have hχ := fun p s h => GlobalTheory.T.natural_sections_linear_extension R ((fibQ q N).obj (op (SimplexCategory.mk p))) (I.X s) (hI s) f hf (ψ p s h) (hψ p s h)
  choose χ hχn hχf using hχ
  refine ⟨⟨buildMor q N I n χ hχn⟩, ?_⟩
  ext U : 4
  refine LinearMap.ext fun a => ?_
  change cochainOfSection q N I n χ hχn U.unop (Sec.map f a) = (g.hom.app U).hom a
  have evExt {E : Spc} (α β : Cochain ((chains R).obj E) I n)
      (he : ∀ p s h W y, ev (R := R) α p s h W y = ev (R := R) β p s h W y) : α = β := by
    ext i s h : 1
    by_cases hi : i ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E p).inv]
      exact free_ext _ _ (fun W y => he p s h W y)
    · exact (isZero_chains E i (by omega)).eq_of_src _ _
  refine evExt _ _ (fun p s h W y => ?_)
  refine (buildC_ev q N I n χ hχn U.unop (Sec.map f a) p s h W y).trans ?_
  refine (congrArg (χ p s h W (y.map prod.snd))
    (_root_.GlobalTheory.EtC.CupSpec.map_res f (show W ⟶ U.unop from y.map prod.fst) a)).trans ?_
  refine (hχf p s h W _ _).trans ?_
  have hn := ConcreteCategory.congr_hom (g.hom.naturality (show W ⟶ U.unop from y.map prod.fst).op) a
  refine (congrArg (fun c => _root_.GlobalTheory.EtC.ev (R := R) (E := sch.obj W ⨯ fibQ q N) (I := I) c p s h W
    (sxPair (schSx (𝟙 W) p) (y.map prod.snd))) hn).trans ?_
  refine (evPull (prod.map (sch.map (show W ⟶ U.unop from y.map prod.fst)) (𝟙 (fibQ q N)))
    ((g.hom.app U).hom a) p s h W _).trans ?_
  congr 1
  rw [sxPair_map]
  exact sxPair_eta y

theorem Jcx_X_injective : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R), (∀ n, CategoryTheory.Injective (I.X n)) →
    ∀ n, CategoryTheory.Injective ((Jcx R q N I).X n) := by
  intro R _ q N I hI n
  have hS := GlobalTheory.T.isSheaf_projBundleCochainPresheaf_etale R q N I n
  exact Injective.of_iso (sheafificationIso (⟨cotPre R q N I n, hS⟩ : Shv R)) (injective_cotSheaf q N I hI n hS)

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSequenceEtaleTateTwistStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_sequence_etale_tateTwist : ∀ (q : ℕ) [NeZero q], ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, Mono κ ∧ κ ≫ ((q : ℤ) • 𝟙 Gm) = 0 ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) ∧ (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) ∧ ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b := by
  first | (exact @GlobalTheory.EtC.kummer_sequence) | (exact GlobalTheory.EtC.kummer_sequence) | (intros; apply GlobalTheory.EtC.kummer_sequence  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelCohomologySubsingleton
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem finite_piTensorProduct_const (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Module.Finite A A']
    (ι : Type) [Fintype ι] : Module.Finite A (PiTensorProduct A fun _ : ι => A') := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := A')
  refine ⟨⟨Finset.univ.image (fun r : ι → S => PiTensorProduct.tprod A (fun i => (r i : A'))), ?_⟩⟩
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  have hm : ∀ i, m i ∈ Submodule.span A (S : Set A') := fun i => hS ▸ Submodule.mem_top
  choose c hc using fun i => (Submodule.mem_span_finset).1 (hm i)
  have hm' : m = fun i => ∑ s ∈ S, c i s • s := funext fun i => ((hc i).2).symm
  rw [hm', MultilinearMap.map_sum_finset]
  refine Submodule.sum_mem _ fun r hr => ?_
  rw [MultilinearMap.map_smul_univ]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [Finset.coe_image]
  refine ⟨fun i => ⟨r i, Fintype.mem_piFinset.1 hr i⟩, by simp, rfl⟩

theorem level_vanish : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 2 ≤ s → s < n →
  Subsingleton (Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) s i) := by
  intro q _ n hyp A _ _ hSH hq A' _ _ hfin k s i hs hsn
  obtain ⟨_, e, -, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  have hT := GlobalTheory.T.tateTwistCohomology_laurent_vanishing_finite_algebra q n hyp A hSH hq (PiTensorProduct A fun _ : Fin (k + 1) => A')
    (finite_piTensorProduct_const A A' (Fin (k + 1))) s i hs hsn
  haveI : Subsingleton (Ht q (disc.obj (yoneda.obj (Spec (CommRingCat.of
    (LaurentPolynomial (PiTensorProduct A fun _ : Fin (k + 1) => A')))))) s i) := hT
  let f := disc.mapIso e
  have inj : Function.Injective (pull (ZMod q) f.hom (tw q i) s) := fun x y h => by
    have h' := congrArg (pull (ZMod q) f.inv (tw q i) s) h
    rwa [← pull_comp, ← pull_comp, Iso.inv_hom_id, pull_id, pull_id] at h'
  exact inj.subsingleton

end GlobalTheory.EtC.GmStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulEigenPartProjectionMatrixEqScalarStatement
section
open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_mul_eigenPartProjectionMatrix_eq_scalar : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
    (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K] (g : B →+* K),
    lieIdeal b βB M ≤ RingHom.ker g → ∀ (i : Fin D.a) (c : 𝓞 D.F),
      (M c).map g * (projMat b βB M i).map g = g (βB (b.t i c)) • (projMat b βB M i).map g := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.RankIdeal.map_mul_projMat_eq_smul) | (exact GlobalTheory.UPel.HT.LieLin.RankIdeal.map_mul_projMat_eq_smul) | (intros; apply GlobalTheory.UPel.HT.LieLin.RankIdeal.map_mul_projMat_eq_smul  <;> assumption)
end

