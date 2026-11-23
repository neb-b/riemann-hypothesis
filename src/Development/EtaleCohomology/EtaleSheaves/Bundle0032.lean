module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0009
public import Development.EtaleCohomology.EtaleSheaves.Bundle0018
public import Development.EtaleCohomology.EtaleSheaves.Bundle0011
public import Development.EtaleCohomology.EtaleSheaves.Bundle0019

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.StepPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.AICAcycPf

namespace LateralTheory.E.StepPf

theorem empty_case {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (hc : Set.range f ∪ Set.range g = Set.univ) [IrreducibleSpace X] (hW : ¬ Nonempty ↥(pullback f g : Scheme.{0})) :
    Set.range f = Set.univ ∨ Set.range g = Set.univ := by
  by_contra hne
  push Not at hne
  have hfne : (Set.range f).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hne.2 (by simpa [h] using hc)
  have hgne : (Set.range g).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hne.1 (by simpa [h] using hc)
  have hirr : IsPreirreducible (Set.univ : Set X) := (IrreducibleSpace.isIrreducible_univ X).isPreirreducible
  obtain ⟨x, -, hxf, hxg⟩ := hirr _ _ f.isOpenEmbedding.isOpen_range g.isOpenEmbedding.isOpen_range
    (by simpa using hfne) (by simpa using hgne)
  obtain ⟨u, rfl⟩ := hxf
  obtain ⟨v, hv⟩ := hxg
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) u v hv.symm
  exact hW ⟨z⟩

theorem acyc_of_surj (q : ℕ) {V X : Scheme.{0}} (g : V ⟶ X) [IsOpenImmersion g] (hg : Set.range g = Set.univ)
    (h : Acyc q (sch.obj V)) : Acyc q (sch.obj X) := by
  have : Surjective g := ⟨Set.range_eq_univ.mp hg⟩
  have : IsIso g := (isIso_iff_isOpenImmersion_and_surjective g).mpr ⟨inferInstance, inferInstance⟩
  exact acyc_of_iso q (asIso g).symm h

theorem Step_of : Step := by
  intro hyp hMV hZ q U V X f g _ _ hc hX hU hV hq hAU hAV hAW
  have hXi : IsIntegral X := hX.1
  by_cases hW : Nonempty ↥(pullback f g : Scheme.{0})
  · have hAW' := hAW hW
    have : IsIntegral U := hU.1
    have := hW
    have : IsIntegral (pullback f g : Scheme.{0}) := isIntegral_of_isOpenImmersion (pullback.fst f g ≫ f)
    have hqU : IsUnit (q : Γ(U, ⊤)) := by
      have := hq.map f.appTop.hom
      simpa using this
    intro n i hn
    obtain ⟨δ, hex, -⟩ := hMV hyp (ZMod q) (tw q i)
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by ring⟩
    have hsU := hAU (m + 1) i hn
    have hsV := hAV (m + 1) i hn
    obtain ⟨-, h2, h3⟩ := hex f g hc m
    constructor
    suffices h0 : ∀ x : Ht q (sch.obj X) (m + 1) i, x = 0 by
      intro a b; rw [h0 a, h0 b]
    intro x
    obtain ⟨w, hw⟩ := (h3 x).mp ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw]
    rcases lt_or_eq_of_le (show (0 : ℤ) ≤ m by omega) with hm | hm
    · have hsW := hAW' m i hm
      rw [Subsingleton.elim w 0, map_zero]
    · subst hm
      rw [h2]
      obtain ⟨a, ha⟩ := (hZ hyp q (pullback.fst f g) hU inferInstance hqU i).2 w
      exact ⟨a, 0, by rw [map_zero, sub_zero]; exact ha.symm⟩
  · rcases empty_case f g hc hW with h | h
    · exact acyc_of_surj q f h hAU
    · exact acyc_of_surj q g h hAV

end LateralTheory.E.StepPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TwFBijPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.TwFBijPf

theorem aeval_res {C : Type} [CommRing C] [IsLocalRing C] (q : ℕ) (x : C) :
    aeval (residue C x) (cyclotomic q ℤ) = residue C (aeval x (cyclotomic q ℤ)) :=
  by
  rw [aeval_def, aeval_def, Polynomial.hom_eval₂]; congr 1

theorem isRoot_iff {K : Type} [CommRing K] (q : ℕ) (x : K) :
    IsRoot (cyclotomic q K) x ↔ aeval x (cyclotomic q ℤ) = 0 := by
  rw [← map_cyclotomic_int, IsRoot, Polynomial.eval_map, aeval_def, algebraMap_int_eq]

theorem res_prim {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {ζ : C}
    (h : aeval ζ (cyclotomic q ℤ) = 0) : IsPrimitiveRoot (residue C ζ) q := by
  haveI : NeZero ((q : ℕ) : ResidueField C) := ⟨by
    have := hq.map (residue C); rw [map_natCast] at this; exact this.ne_zero⟩
  rw [← isRoot_cyclotomic_iff, isRoot_iff]
  exact (aeval_res q ζ).trans (by rw [h, map_zero])

theorem pow_q {C : Type} [CommRing C] {q : ℕ} {ζ : C} (h : aeval ζ (cyclotomic q ℤ) = 0) : ζ ^ q = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval ζ) hg
  simp [h] at this
  exact sub_eq_zero.1 this

theorem prim {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {ζ : C}
    (h : aeval ζ (cyclotomic q ℤ) = 0) : IsPrimitiveRoot ζ q := by
  refine ⟨pow_q h, fun l hl => (res_prim hq h).dvd_of_pow_eq_one l ?_⟩
  rw [← map_pow, hl, map_one]

theorem uniq {C : Type} [CommRing C] [IsLocalRing C] {n : ℕ} (hn : IsUnit (n : C)) {x y : C} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (hr : residue C x = residue C y) : x = y := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have key := (Commute.all x y).geom_sum₂_mul n
  rw [hx, hy, sub_self] at key
  have hS : IsUnit (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← residue_ne_zero_iff_isUnit, map_sum]
    have : ∀ i ∈ Finset.range n, residue C (x ^ i * y ^ (n - 1 - i)) = residue C x ^ (n - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, ← hr, ← pow_add]
      congr 1
      have := Finset.mem_range.1 hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 : IsUnit (residue C (n : C)) := hn.map _
    have h2 : IsUnit (residue C x) := (show IsUnit x from ⟨⟨x, x ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), hx],
      by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), hx]⟩, rfl⟩).map _
    rw [map_natCast] at h1
    exact (h1.mul (h2.pow _)).ne_zero
  have := hS.mul_right_eq_zero.1 key
  exact sub_eq_zero.1 this

theorem pow_rep {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {η ξ : C}
    (hη : aeval η (cyclotomic q ℤ) = 0) (hξ : aeval ξ (cyclotomic q ℤ) = 0) :
    ∃ a : (ZMod q)ˣ, ξ = η ^ (a : ZMod q).val := by
  obtain ⟨i, hi, he⟩ := (res_prim hq hη).eq_pow_of_pow_eq_one (ξ := residue C ξ) (by rw [← map_pow, pow_q hξ, map_one])
  have hηi : η ^ i = ξ := uniq hq (by rw [← pow_mul, mul_comm, pow_mul, pow_q hη, one_pow]) (pow_q hξ) (by rw [map_pow, he])
  have hc : i.Coprime q := ((prim hq hη).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hηi ▸ prim hq hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hηi]

theorem pow_inj {C : Type} [CommRing C] {q : ℕ} [NeZero q] {η : C} (hη : IsPrimitiveRoot η q) {a b : (ZMod q)ˣ}
    (h : η ^ (a : ZMod q).val = η ^ (b : ZMod q).val) : a = b :=
  Units.ext (ZMod.val_injective q (hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))

theorem exists_root {A : Type} [CommRing A] {q : ℕ} [NeZero q] (hq : IsUnit (q : A)) (hA : SH A) :
    ∃ ζ : A, aeval ζ (cyclotomic q ℤ) = 0 := by
  obtain ⟨hH, hS⟩ := hA
  haveI : NeZero ((q : ℕ) : ResidueField A) := ⟨by
    have := hq.map (residue A); rw [map_natCast] at this; exact this.ne_zero⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root (cyclotomic q (ResidueField A))
    (ne_of_gt (degree_cyclotomic_pos q _ (Nat.pos_of_ne_zero (NeZero.ne q)))) (separable_cyclotomic q _)
  obtain ⟨a0, rfl⟩ := residue_surjective x
  have hd : IsUnit ((cyclotomic q A).derivative.eval a0) := by
    rw [← residue_ne_zero_iff_isUnit]
    have := (separable_cyclotomic q (ResidueField A)).aeval_derivative_ne_zero (x := residue A a0) (by
      rw [aeval_def, Algebra.algebraMap_self, eval₂_id]; exact hx)
    rw [aeval_def, Algebra.algebraMap_self, eval₂_id, ← map_cyclotomic q (residue A), derivative_map,
      Polynomial.eval_map, Polynomial.eval₂_hom] at this
    exact this
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (cyclotomic q A) (cyclotomic.monic q A) a0 (by
    rw [← residue_eq_zero_iff, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, map_cyclotomic]; exact hx) hd
  exact ⟨a, (isRoot_iff q a).1 ha⟩

section Gen
variable {q : ℕ} [NeZero q] (i : ℤ) {C : Type} [CommRing C] [IsLocalRing C]

theorem pmod {η : C} (hη : IsPrimitiveRoot η q) (n : ℕ) : η ^ (n % q) = η ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, hη.pow_eq_one, one_pow, mul_one]

def ex (η ξ : Prim q C) : (ZMod q)ˣ := Classical.choose (pow_rep η.2.1 η.2.2 ξ.2.2)

theorem ex_spec (η ξ : Prim q C) : ξ.1 = η.1 ^ (ex η ξ : ZMod q).val := Classical.choose_spec (pow_rep η.2.1 η.2.2 ξ.2.2)

theorem ex_pow (η ξ ζ : Prim q C) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : ex η ξ = ex η ζ * a := by
  have hη := prim η.2.1 η.2.2
  apply pow_inj hη
  rw [← ex_spec, h, ex_spec η ζ, ← pow_mul, Units.val_mul, ZMod.val_mul, pmod hη]

theorem ex_self (η : Prim q C) : ex η η = 1 := by
  have hη := prim η.2.1 η.2.2
  apply pow_inj hη
  rw [← ex_spec, Units.val_one, ZMod.val_one_eq_one_mod, pmod hη, pow_one]

def psi (η : Prim q C) : (Prim q C →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (fun ξ => ULift.up (((ex η ξ ^ i : (ZMod q)ˣ) : ZMod q)))

theorem rel_le (η : Prim q C) : twRel q i C ≤ LinearMap.ker (psi i η) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, psi, Finsupp.linearCombination_single, ex_pow η ξ ζ a h,
    mul_zpow, Units.val_mul]
  apply ULift.ext
  simp [mul_comm]

def Psi (η : Prim q C) : ((Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  (twRel q i C).liftQ (psi i η) (rel_le i η)

def gen (η : Prim q C) : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C := Submodule.Quotient.mk (Finsupp.single η 1)

theorem Psi_gen (η : Prim q C) : Psi i η (gen i η) = 1 := by
  simp [Psi, gen, psi, Finsupp.linearCombination_single, ex_self]
  rfl

theorem decomp (η : Prim q C) (z : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) : z = Psi i η z • gen i η := by
  induction z using Submodule.Quotient.induction_on with
  | H x =>
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Submodule.Quotient.mk_add, map_add (f := _), add_smul, ← hx, ← hy]
  | single ξ c =>
    have hrel : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single η (ULift.up (((ex η η * ex η ξ) ^ i : (ZMod q)ˣ) : ZMod q))
        ∈ twRel q i C := by
      refine Submodule.subset_span ⟨η, ξ, ex η ξ, ex_spec η ξ, ?_⟩
      rw [ex_self, one_mul]
    rw [ex_self, one_mul] at hrel
    have h1 : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) =
        ULift.up (((ex η ξ ^ i : (ZMod q)ˣ) : ZMod q)) • gen i η := by
      rw [gen, ← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
      exact (Submodule.Quotient.eq _).2 hrel
    have h2 : (Finsupp.single ξ c : Prim q C →₀ ULift.{1} (ZMod q)) = c • Finsupp.single ξ 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h2, Submodule.Quotient.mk_smul, h1, smul_smul]
    congr 1
    rw [map_smul, Psi_gen, smul_eq_mul, mul_one]

end Gen

theorem bij_ty {q : ℕ} [NeZero q] (i : ℤ) {X Y : Type} [CommRing X] [CommRing Y] [IsLocalRing X] [IsLocalRing Y]
    (g : X →+* Y) (ζ : Prim q X) :
    Function.Bijective (Submodule.mapQ (twRel q i X) (twRel q i Y) (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
      (Prim.map g)) (twRel_le q i g)) := by
  set F := Submodule.mapQ (twRel q i X) (twRel q i Y) (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
      (Prim.map g)) (twRel_le q i g)
  have hF : ∀ z, F z = Psi i ζ z • gen i (Prim.map g ζ) := by
    intro z
    conv_lhs => rw [decomp i ζ z]
    rw [map_smul]
    congr 1
    simp only [F, gen, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  have hP : ∀ z, Psi i (Prim.map g ζ) (F z) = Psi i ζ z := by
    intro z
    rw [hF, map_smul, Psi_gen, smul_eq_mul, mul_one]
  refine ⟨fun z1 z2 h => ?_, fun w => ⟨Psi i (Prim.map g ζ) w • gen i ζ, ?_⟩⟩
  · rw [decomp i ζ z1, decomp i ζ z2, ← hP z1, ← hP z2, h]
  · rw [hF, map_smul, Psi_gen, smul_eq_mul, mul_one]
    exact (decomp i _ w).symm

theorem bij_gen {q : ℕ} [NeZero q] (i : ℤ) {X Y : CommRingCat.{0}} [IsLocalRing X] [IsLocalRing Y] (g : X ⟶ Y)
    (ζ : Prim q X) : Function.Bijective ((twF q i).map g).hom :=
  bij_ty i g.hom ζ

theorem TwFBij_of : LateralTheory.E.SHEqvPf.TwFBij := by
  intro q _ i A B f hq hA hB
  obtain ⟨hHA, hSA⟩ := hA
  obtain ⟨hHB, -⟩ := hB
  have hloc : ∀ (R : CommRingCat.{0}), IsLocalRing R → IsLocalRing Γ(Spec R, ⊤) := by
    intro R _
    let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
    haveI : Nontrivial Γ(Spec R, ⊤) := e.toEquiv.nontrivial
    exact IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  haveI := hloc A inferInstance
  haveI := hloc B inferInstance
  obtain ⟨ζ, hζ⟩ := exists_root hq ⟨hHA, hSA⟩
  exact bij_gen i _ (Prim.map (Scheme.ΓSpecIso A).inv.hom ⟨ζ, hq, hζ⟩)

end LateralTheory.E.TwFBijPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TwGenNZACPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.TwGenNZACPf

section Field
variable {q : ℕ} [NeZero q] {L : Type} [Field L]

theorem prim_isPrimitiveRoot (z : Prim q L) : IsPrimitiveRoot z.1 q := by
  have : NeZero (q : L) := ⟨z.2.1.ne_zero⟩
  have h := z.2.2
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] at h
  exact Polynomial.isRoot_cyclotomic_iff.1 h


open Classical in
def lg (q : ℕ) (z x : L) : ZMod q := if h : ∃ n : ℕ, z ^ n = x then (h.choose : ZMod q) else 0

theorem lg_pow {z : L} (hz : IsPrimitiveRoot z q) (n : ℕ) : lg q z (z ^ n) = n := by
  have h : ∃ m : ℕ, z ^ m = z ^ n := ⟨n, rfl⟩
  unfold lg
  rw [dite_eq_left h, ZMod.natCast_eq_natCast_iff]
  have h2 := h.choose_spec
  have h3 := ((hz.isOfFinOrder (NeZero.ne q)).pow_eq_pow_iff_modEq).1 h2
  rwa [← hz.eq_orderOf] at h3


open Classical in
def fv (q : ℕ) (i : ℤ) (z x : L) : ZMod q :=
  if h : IsUnit (lg q z x) then ((h.unit ^ i : (ZMod q)ˣ) : ZMod q) else 0

theorem fv_rel (i : ℤ) (z : Prim q L) (ζ ξ : Prim q L) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    fv q i z.1 ξ.1 = ((a ^ i : (ZMod q)ˣ) : ZMod q) * fv q i z.1 ζ.1 := by
  have hz := prim_isPrimitiveRoot z
  obtain ⟨m, -, hm⟩ := hz.eq_pow_of_pow_eq_one (prim_isPrimitiveRoot ζ).pow_eq_one
  have hl : lg q z.1 ξ.1 = lg q z.1 ζ.1 * a := by
    rw [h, ← hm, ← pow_mul, lg_pow hz, lg_pow hz]
    push_cast
    rw [ZMod.natCast_zmod_val]
  unfold fv
  by_cases hu : IsUnit (lg q z.1 ζ.1)
  · have hu' : IsUnit (lg q z.1 ξ.1) := hl ▸ hu.mul a.isUnit
    rw [dite_eq_left hu, dite_eq_left hu']
    have : hu'.unit = hu.unit * a := Units.ext (by simp [hl])
    rw [this, mul_zpow, Units.val_mul, mul_comm]
  · have hu' : ¬ IsUnit (lg q z.1 ξ.1) := by
      rw [hl]; exact fun h' => hu ((Units.isUnit_mul_units _ a).1 h')
    rw [dite_eq_right hu, dite_eq_right hu', mul_zero]

theorem fv_self (i : ℤ) (z : Prim q L) : fv q i z.1 z.1 = 1 := by
  have hl : lg q z.1 z.1 = 1 := by
    have := lg_pow (prim_isPrimitiveRoot z) 1
    rw [pow_one] at this
    rw [this, Nat.cast_one]
  unfold fv
  have hu : IsUnit (lg q z.1 z.1) := hl ▸ isUnit_one
  rw [dite_eq_left hu]
  have : hu.unit = 1 := Units.ext (by simp [hl])
  rw [this, one_zpow, Units.val_one]

def lin (i : ℤ) (z : L) : (Prim q L →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (fun ξ : Prim q L => ULift.up (fv q i z ξ.1))

theorem lin_rel (i : ℤ) (z : Prim q L) : twRel q i L ≤ LinearMap.ker (lin i z.1) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, lin, Finsupp.linearCombination_single]
  rw [sub_eq_zero]
  apply ULift.ext
  simp [fv_rel i z ζ ξ a h]

theorem field_nz (i : ℤ) (z : Prim q L) (c : ZMod q)
    (h : c.val • (Submodule.Quotient.mk (Finsupp.single z 1) : (Prim q L →₀ ULift.{1} (ZMod q)) ⧸ twRel q i L) = 0) :
    c = 0 := by
  have h2 := congrArg ((twRel q i L).liftQ (lin i z.1) (lin_rel i z)) h
  rw [map_nsmul, Submodule.liftQ_apply, map_zero, lin, Finsupp.linearCombination_single, fv_self] at h2
  rw [one_smul] at h2
  have h3 := congrArg AddEquiv.ulift h2
  rw [map_nsmul, map_zero] at h3
  change c.val • (1 : ZMod q) = 0 at h3
  rwa [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] at h3

end Field

theorem ring_nz {q : ℕ} [NeZero q] (i : ℤ) {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (c : ZMod q)
    (h : c.val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) = 0) :
    c = 0 := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let _ := Ideal.Quotient.field M
  apply field_nz i (ζ.map (Ideal.Quotient.mk M)) c
  have h2 := congrArg (Submodule.mapQ _ _ (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
    (Prim.map (Ideal.Quotient.mk M))) (twRel_le q i (Ideal.Quotient.mk M))) h
  rw [map_nsmul, map_zero, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] at h2
  exact h2

theorem gamma_nontrivial (V : Scheme.{0}) [Nonempty V] : Nontrivial Γ(V, ⊤) := by
  obtain ⟨y⟩ := ‹Nonempty V›
  exact RingHom.domain_nontrivial (V.presheaf.germ ⊤ y trivial).hom

theorem TwGenNZAC_of : LateralTheory.E.LCBijPf.TwGenNZAC := by
  intro q _ i K _ _ ζ c h
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q i
  let U : Scheme.{0} := Spec (CommRingCat.of K)
  let m : P.obj (op U) := Submodule.Quotient.mk (Finsupp.single (gam ζ) 1)
  have h1 : ((toSheafify Scheme.etaleTopology P).app (op U)).hom (c.val • m) =
      ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0 := by
    rw [map_nsmul, map_zero]
    exact h
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c.val • m) 0 h1
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  obtain ⟨p⟩ : Nonempty U := inferInstance
  obtain ⟨j, y, -⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 p
  have hj := hle _ _ (Presieve.ofArrows.mk j)
  have : Nonempty (𝒰.X j) := ⟨y⟩
  have : Nontrivial (Scheme.Γ.obj (op (𝒰.X j))) := gamma_nontrivial (𝒰.X j)
  apply ring_nz i ((gam ζ).map (Scheme.Γ.map (𝒰.f j).op).hom) c
  change (P.map (𝒰.f j).op).hom (c.val • m) = (P.map (𝒰.f j).op).hom 0 at hj
  rw [map_nsmul, map_zero] at hj
  change c.val • Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map (𝒰.f j).op).hom)
    (Finsupp.single (gam ζ) 1)) = _ at hj
  erw [Finsupp.mapDomain_single] at hj
  exact hj

end LateralTheory.E.TwGenNZACPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TwistGenerators
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitSecPf

def LeafTwGenIndep : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), twGen 0 ζ = twGen 0 ξ

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map (Scheme.Γ.map g.op).hom) := by
  unfold twGen ofRings.sec
  have h := congrArg (fun t => t.hom (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  refine h.symm.trans (congrArg (fun y => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom y) ?_)
  exact congrArg (Submodule.Quotient.mk (p := twRel q i Γ(V, ⊤))) (Finsupp.mapDomain_single (f := Prim.map (Scheme.Γ.map g.op).hom))

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (k : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res k x) = Sec.res (h ≫ k) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  show (F.obj.map (𝟙 U).op).hom x = x
  rw [op_id, F.obj.map_id]
  rfl

theorem tw_isSheafFor (q : ℕ) (U : Scheme.{0}) (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) :
    Presieve.IsSheafFor ((tw q 0).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) S.arrows := by
  have hF := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology (tw q 0).obj
    (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))).1 (tw q 0).property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact hF S hS

section Glue

def cov (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Sieve U := Classical.choose (hP q U hU)

theorem cov_mem (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : cov hP q U hU ∈ Scheme.etaleTopology U :=
  (Classical.choose_spec (hP q U hU)).1

theorem cov_prim (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (V : Scheme.{0}) (g : V ⟶ U) (hg : (cov hP q U hU).arrows g) :
    Nonempty (Prim q Γ(V, ⊤)) :=
  (Classical.choose_spec (hP q U hU)).2 V g hg

def fam (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) :
    Presieve.FamilyOfElements ((tw q 0).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) (cov hP q U hU).arrows :=
  fun V g hg => twGen 0 (Classical.choice (cov_prim hP q U hU V g hg))

theorem fam_compat (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : (fam hP q U hU).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Y Z f g hf
  change _ = Sec.res g (twGen 0 _)
  rw [twGen_res]
  exact hI q Z _ _

def one (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Sec (tw q 0) U :=
  (tw_isSheafFor q U _ (cov_mem hP q U hU)).amalgamate (fam hP q U hU) (fam_compat hP hI q U hU)

theorem one_char (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (W : Scheme.{0}) (k : W ⟶ U) (ζ : Prim q Γ(W, ⊤)) :
    Sec.res k (one hP hI q U hU) = twGen 0 ζ := by
  refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) W ((cov hP q U hU).pullback k)
    (Scheme.etaleTopology.pullback_stable k (cov_mem hP q U hU)) _ _ fun V h hh => ?_
  rw [res_comp, twGen_res]
  have hv := (tw_isSheafFor q U _ (cov_mem hP q U hU)).valid_glue (fam_compat hP hI q U hU) (h ≫ k) hh
  refine hv.trans ?_
  exact hI q V _ _

end Glue

theorem LeafUnitSec_of (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) :
    LateralTheory.E.LeafOneExistsPf.LeafUnitSec := by
  intro q _
  refine ⟨one hP hI q, fun V U g hU hV => ?_, fun U hU ζ => ?_⟩
  · refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) V (cov hP q V hV) (cov_mem hP q V hV) _ _ fun W h hh => ?_
    obtain ⟨ζ⟩ := cov_prim hP q V hV W h hh
    rw [res_comp, one_char hP hI q U hU W _ ζ, one_char hP hI q V hV W h ζ]
  · rw [← one_char hP hI q U hU U (𝟙 U) ζ, res_id]

end LateralTheory.E.LeafUnitSecPf
end
end

