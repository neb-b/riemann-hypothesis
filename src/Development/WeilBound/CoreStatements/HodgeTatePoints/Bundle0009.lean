module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
public import ReciprocityTheory.DualLattices.Bundle0012
public import ReciprocityTheory.DualLattices.UpSmith

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FormMemLin
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

section
variable {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]

def formR (p : ℕ) (ι : Type) [Fintype ι] : (ι → R) →ₗ[R] ((ι → ZMod p) → R) where
  toFun l x := ∑ i, l i * ((x i).val : R)
  map_add' l l' := by ext x; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c l := by ext x; simp [Finset.mul_sum, mul_assoc]


variable (C) in
def toC (X : Type) : (X → R) →ₗ[R] (X → C) := (Algebra.linearMap R C).compLeft X

variable {R}

theorem mem_pInt {p : ℕ} {z : C} : z ∈ pInt (C := C) R p ↔ ∃ r : R, z = algebraMap R C r * p := by
  simp only [pInt, Submodule.mem_span_singleton, Algebra.smul_def]
  exact ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩

theorem afLat_eq (p : ℕ) {ι : Type} [Fintype ι] (M : Submodule R ((ι → ZMod p) → C)) :
    afLat p M = (M ⊔ pFun R p _).comap (toC (C := C) R _ ∘ₗ formR R p ι) := by
  ext l
  rw [Submodule.mem_comap, Submodule.mem_sup]
  change (∃ g ∈ M, ∀ x, g x - algebraMap R C (∑ i, l i * ((x i).val : R)) ∈ pInt R p) ↔ _
  have hf : (toC (C := C) R _ ∘ₗ formR R p ι) l = fun x => algebraMap R C (∑ i, l i * ((x i).val : R)) := rfl
  rw [hf]
  constructor
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, fun x => algebraMap R C (∑ i, l i * ((x i).val : R)) - g x, ?_, ?_⟩
    · rw [pFun, Submodule.mem_pi]
      intro x _
      have := neg_mem (h x)
      rwa [neg_sub] at this
    · funext x
      simp
  · rintro ⟨g, hg, z, hz, he⟩
    refine ⟨g, hg, fun x => ?_⟩
    have hx : z x ∈ pInt R p := (Submodule.mem_pi.mp hz) x (Set.mem_univ x)
    have e : g x - algebraMap R C (∑ i, l i * ((x i).val : R)) = - z x := by
      rw [← congrFun he x]
      simp
    rw [e]
    exact neg_mem hx

theorem form_mem_lin (p : ℕ) [NeZero p] {ι : Type} [Fintype ι] (l : ι → R) :
    (toC (C := C) R _ ∘ₗ formR R p ι) l ∈ linFun (C := C) R p (ι → ZMod p) := by
  rw [linFun, Submodule.mem_inf]
  have hf : (toC (C := C) R _ ∘ₗ formR R p ι) l = fun x => algebraMap R C (∑ i, l i * ((x i).val : R)) := rfl
  rw [hf]
  refine ⟨fun x => ⟨∑ i, l i * ((x i).val : R), rfl⟩, ?_⟩
  intro x y
  rw [mem_pInt]
  refine ⟨-∑ i, l i * ((((x i).val + (y i).val) / p : ℕ) : R), ?_⟩
  have key : ∀ i, (((x i + y i).val : ℕ) : R) = ((x i).val : R) + (y i).val - p * ((((x i).val + (y i).val) / p : ℕ) : R) := by
    intro i
    rw [ZMod.val_add, eq_sub_iff_add_eq, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div, Nat.cast_add]
  simp only [Pi.add_apply, key]
  simp only [← map_sub, ← map_neg, ← map_natCast (algebraMap R C), ← map_mul]
  congr 1
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem add_mem_pFun {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    {h : (ι → ZMod p) → C} (hh : h ∈ addFun R p (ι → ZMod p))
    (h1 : ∀ i, h (Pi.single i 1) ∈ pInt (C := C) R p) : h ∈ pFun R p (ι → ZMod p) := by
  have h0 : h 0 ∈ pInt (C := C) R p := by
    have := neg_mem (hh 0 0)
    simpa using this
  let S : AddSubmonoid (ι → ZMod p) :=
    { carrier := {x | h x ∈ pInt (C := C) R p}
      add_mem' := by
        intro a b ha hb
        have e : h (a + b) = (h (a + b) - h a - h b) + h a + h b := by ring
        show h (a + b) ∈ pInt (C := C) R p
        rw [e]
        exact add_mem (add_mem (hh a b) ha) hb
      zero_mem' := h0 }
  have hall : ∀ x, x ∈ S := by
    intro x
    rw [← Finset.univ_sum_single x]
    refine sum_mem fun i _ => ?_
    have e : Pi.single i (x i) = (x i).val • (Pi.single i (1 : ZMod p) : ι → ZMod p) := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_apply, hj]
    rw [e]
    exact nsmul_mem (show (Pi.single i (1 : ZMod p) : ι → ZMod p) ∈ S from h1 i) _
  rw [pFun, Submodule.mem_pi]
  intro x _
  exact hall x

end

theorem aflat_fg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), (afLat p AA.carrier).FG := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI : ValuationRing R :=
    { cond' := fun a b => by
        rcases le_total (v (algebraMap R C a)) (v (algebraMap R C b)) with h | h
        · obtain ⟨c, hc⟩ := hv.dvd_of_le h
          exact ⟨c, Or.inr hc.symm⟩
        · obtain ⟨c, hc⟩ := hv.dvd_of_le h
          exact ⟨c, Or.inl hc.symm⟩ }
  rw [afLat_eq, Submodule.comap_comp]
  apply comap_fg_of_valuationRing
  have hinj : Function.Injective (toC (C := C) R (ι → ZMod p)) := by
    intro f g h
    funext x
    exact hv.hom_inj (congrFun h x)
  apply Submodule.fg_of_fg_map_injective (toC (C := C) R (ι → ZMod p)) hinj
  have hle : AA.carrier ⊔ pFun R p (ι → ZMod p) ≤ LinearMap.range (toC (C := C) R (ι → ZMod p)) := by
    apply sup_le
    · intro f hf
      have hi := AA.le_int hf
      choose r hr using hi
      exact ⟨r, funext fun x => hr x⟩
    · intro f hf
      rw [pFun, Submodule.mem_pi] at hf
      choose r hr using fun x => mem_pInt.mp (hf x (Set.mem_univ x))
      refine ⟨fun x => r x * p, funext fun x => ?_⟩
      rw [hr x]
      simp [toC]
  rw [Submodule.map_comap_eq, inf_eq_right.mpr hle]
  apply Submodule.FG.sup
  · obtain ⟨B, _, hB⟩ := AA.lat
    rw [hB]
    exact Submodule.fg_span (Set.finite_range _)
  · have hP : pFun R p (ι → ZMod p) = Submodule.map ((p : R) • toC (C := C) R (ι → ZMod p)) ⊤ := by
      ext f
      simp only [Submodule.mem_map, Submodule.mem_top, true_and]
      rw [pFun, Submodule.mem_pi]
      constructor
      · intro hf
        choose r hr using fun x => mem_pInt.mp (hf x (Set.mem_univ x))
        refine ⟨r, funext fun x => ?_⟩
        rw [hr x]
        simp [toC, Algebra.smul_def, mul_comm]
      · rintro ⟨r, rfl⟩ x _
        rw [mem_pInt]
        exact ⟨r x, by simp [toC, Algebra.smul_def, mul_comm]⟩
    rw [hP]
    exact Submodule.FG.map _ Module.Finite.fg_top

theorem afquot : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier)) := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let φ := toC (C := C) R (ι → ZMod p) ∘ₗ formR R p ι
  let K := Submodule.comap (linFun (C := C) R p (ι → ZMod p)).subtype (afFun p AA.carrier ⊔ pFun (C := C) R p (ι → ZMod p))
  let ψ : (ι → R) →ₗ[R] linFun (C := C) R p (ι → ZMod p) := LinearMap.codRestrict _ φ (fun l => form_mem_lin p l)
  let f := K.mkQ ∘ₗ ψ
  have hpf : pFun (C := C) R p (ι → ZMod p) ≤ addFun (C := C) R p (ι → ZMod p) := by
    intro z hz x y
    rw [pFun, Submodule.mem_pi] at hz
    exact sub_mem (sub_mem (hz _ (Set.mem_univ _)) (hz _ (Set.mem_univ _))) (hz _ (Set.mem_univ _))
  have hker : afLat p AA.carrier = LinearMap.ker f := by
    ext l
    rw [LinearMap.mem_ker, afLat_eq, Submodule.mem_comap]
    change _ ↔ Submodule.Quotient.mk (ψ l) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    change φ l ∈ AA.carrier ⊔ pFun (C := C) R p _ ↔ φ l ∈ afFun p AA.carrier ⊔ pFun (C := C) R p _
    constructor
    · intro h
      obtain ⟨g, hg, z, hz, he⟩ := Submodule.mem_sup.mp h
      have hadd : φ l ∈ addFun (C := C) R p (ι → ZMod p) := (Submodule.mem_inf.mp (form_mem_lin p l)).2
      have hg' : g ∈ addFun (C := C) R p (ι → ZMod p) := by
        have : g = φ l - z := by rw [← he]; abel
        rw [this]
        exact sub_mem hadd (hpf hz)
      exact Submodule.mem_sup.mpr ⟨g, Submodule.mem_inf.mpr ⟨hg, hg'⟩, z, hz, he⟩
    · intro h
      exact (sup_le_sup_right inf_le_left _ : afFun p AA.carrier ⊔ pFun (C := C) R p _ ≤ AA.carrier ⊔ pFun (C := C) R p _) h
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨⟨h, hh⟩, rfl⟩ := Submodule.mkQ_surjective K q
    have hh' := Submodule.mem_inf.mp hh
    choose l hl using fun i => hh'.1 (Pi.single i (1 : ZMod p))
    refine ⟨l, ?_⟩
    show Submodule.Quotient.mk (ψ l) = Submodule.Quotient.mk ⟨h, hh⟩
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    apply Submodule.mem_sup_right
    change φ l - h ∈ pFun (C := C) R p (ι → ZMod p)
    apply add_mem_pFun
    · exact sub_mem (Submodule.mem_inf.mp (form_mem_lin p l)).2 hh'.2
    · intro i
      have e : φ l (Pi.single i 1) = algebraMap R C (l i) := by
        show algebraMap R C (∑ j, l j * (((Pi.single i (1 : ZMod p) : ι → ZMod p) j).val : R)) = _
        simp [Pi.single_apply, apply_ite, ZMod.val_one]
      rw [Pi.sub_apply, e, hl i, sub_self]
      exact zero_mem _
  exact ⟨((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective f hsurj)).symm⟩

end PositivityTheory.HtPt.Rh
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.PowCongr
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem powadd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal) (x y z : C), v x ≤ 1 → v y ≤ 1 → v (z - x - y) ≤ v (p : C) → v (z ^ p - x ^ p - y ^ p) ≤ v (p : C) := by
  intro p hp C _ v x y z hx hy h
  have hp1 : v (p : C) ≤ 1 := by
    exact natCast_mem v.integer p
  have hz : v z ≤ 1 := by
    have e : z = (z - x - y) + x + y := by ring
    rw [e]
    exact v.map_add_le (v.map_add_le (h.trans hp1) hx) hy
  let X : v.integer := ⟨x, hx⟩
  let Y : v.integer := ⟨y, hy⟩
  let Z : v.integer := ⟨z, hz⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out X Y
  obtain ⟨s, hs⟩ := sub_dvd_pow_sub_pow Z (X + Y) p
  have hr' := congrArg v.integer.subtype hr
  have hs' := congrArg v.integer.subtype hs
  simp only [map_add (f := _), map_mul, map_pow, map_sub, map_natCast, Subring.subtype_apply, X, Y, Z]
    at hr' hs'
  have e : z ^ p - x ^ p - y ^ p = (z - x - y) * (s : C) + (p : C) * (x * y * (r : C)) := by
    linear_combination hr' + hs'
  rw [e]
  refine v.map_add_le ?_ ?_
  · rw [map_mul]
    exact (mul_le_of_le_one_right' (α := NNReal) s.2).trans h
  · rw [map_mul]
    refine mul_le_of_le_one_right' ?_
    rw [map_mul, map_mul]
    exact mul_le_one' (mul_le_one' hx hy) r.2

section

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem mem_pInt [CharZero C] (hv : v.Integers R) {p : ℕ} (hp : p ≠ 0) (x : C) :
    x ∈ pInt (C := C) R p ↔ v x ≤ v (p : C) := by
  have h0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp
  rw [pInt, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    rw [Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_left' (hv.map_le_one r)
  · intro h
    have h1 : v (x / p) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ h zero_le
    obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
    exact ⟨r, by rw [Algebra.smul_def, hr, div_mul_cancel₀ _ h0]⟩

theorem val_le_one (hv : v.Integers R) {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {g : N → C} (hg : g ∈ AA.carrier) (x : N) : v (g x) ≤ 1 := by
  obtain ⟨r, hr⟩ := AA.le_int hg x
  rw [← hr]
  exact hv.map_le_one r

theorem pow_mem {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {g : N → C} (hg : g ∈ AA.carrier) (k : ℕ) :
    g ^ k ∈ AA.carrier := by
  induction k with
  | zero => rw [pow_zero]; exact AA.one_mem
  | succ k ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hg

theorem pow_congr (p : ℕ) [hp : Fact p.Prime] {x z : C} (hx : v x ≤ 1)
    (h : v (z - x) ≤ v (p : C)) : v (z ^ p - x ^ p) ≤ v (p : C) := by
  have := powadd p C v x 0 z hx (by simp) (by simpa using h)
  simpa [zero_pow hp.out.ne_zero] using this

end

theorem a_pow : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) := by
  intro p hp C _ _ _ v R _ _ hv hp1 F _ _ _ _ f hF N _ _ _ _ AA hst K t τ c hc
  obtain ⟨g, ⟨hg, hadd⟩, h1, h2, h3⟩ := hc
  have hp0 := hp.out.ne_zero
  have hb := val_le_one hv AA hg
  refine ⟨g ^ p, ⟨pow_mem AA hg p, fun x y => ?_⟩, fun a x => ?_, fun k hk => ?_, ?_⟩
  · rw [mem_pInt hv hp0]
    exact powadd p C v _ _ _ (hb x) (hb y) ((mem_pInt hv hp0 _).1 (hadd x y))
  · rw [mem_pInt hv hp0, MulChar.pow_apply' _ hp0, map_pow, Pi.pow_apply, Pi.pow_apply, ← mul_pow]
    refine pow_congr p ?_ ((mem_pInt hv hp0 _).1 (h1 a x))
    rw [map_mul]
    exact mul_le_one' (hv.map_le_one _) (hb x)
  · rw [mem_pInt hv hp0]
    have := pow_congr (v := v) p (x := 0) (z := g k) (by simp)
      (by simpa using (mem_pInt hv hp0 _).1 (h2 k hk))
    simpa [zero_pow hp0] using this
  · rw [mem_pInt hv hp0, map_pow, Pi.pow_apply]
    exact pow_congr p (hv.map_le_one _) ((mem_pInt hv hp0 _).1 h3)

end PositivityTheory.HtPt.Rd
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RaChar
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

theorem charmem : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ ψ : AddChar N C, (fun x => ψ x) ∈ AA.carrier := by
  intro p _ C _ _ _ v R _ _ hv _ N _ _ _ AA ψ
  obtain ⟨B, hB, hAA⟩ := AA.lat
  rw [hAA, ← dualLat_dualLat_spanCols B hB, ← hAA]
  intro u hu
  obtain ⟨r, hr⟩ := hv.exists_of_le_one
    (valuation_fourier_le_one v hv (fun _ : Unit => ψ) AA hu ())
  refine ⟨r, hr.trans ?_⟩
  rw [fourier_apply']
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end PositivityTheory.HtPt.Ra
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RbTriang
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rb

theorem triang_strong (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (n : ℕ) (L : Submodule R (Fin n → R)) (hL : L.FG) :
    ∃ d : Fin n → R, (∀ i c, c ∈ Ideal.span {d i} ↔ ∃ l ∈ L, (∀ j, j < i → l j = 0) ∧ l i = c) ∧
      HasLen v R ((Fin n → R) ⧸ L) (∏ i, v (algebraMap R C (d i))) := by
  classical
  haveI : IsDomain R := hv.hom_inj.isDomain
  haveI : ValuationRing R := ValuationRing.of_integers v hv
  obtain ⟨m, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  let ψ : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R w
  have hψ : LinearMap.range ψ = L := by rw [Fintype.range_linearCombination, hw]
  have key : ∀ i : Fin n, ∃ d : R,
      ∀ c, c ∈ Ideal.span {d} ↔ ∃ l ∈ L, (∀ j, j < i → l j = 0) ∧ l i = c := by
    intro i
    let π : (Fin n → R) →ₗ[R] ({j : Fin n // j < i} → R) := LinearMap.funLeft R R Subtype.val
    have h1 := comap_fg_of_valuationRing R (Fin m) {j : Fin n // j < i} (π ∘ₗ ψ) ⊥
      Submodule.fg_bot
    have h2 : Ideal.FG (R := R) (((⊥ : Submodule R _).comap (π ∘ₗ ψ)).map
        (LinearMap.proj i ∘ₗ ψ)) := h1.map _
    obtain ⟨d, hd⟩ := (IsBezout.isPrincipal_of_FG _ h2).principal
    refine ⟨d, fun c => ?_⟩
    have : Ideal.span {d} = ((⊥ : Submodule R _).comap (π ∘ₗ ψ)).map
        (LinearMap.proj i ∘ₗ ψ) := hd.symm
    rw [this]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨ψ a, hψ ▸ LinearMap.mem_range_self ψ a, fun j hj => ?_, rfl⟩
      exact congrFun (show π (ψ a) = 0 from ha) ⟨j, hj⟩
    · rintro ⟨l, hl, h0, rfl⟩
      rw [← hψ] at hl
      obtain ⟨a, rfl⟩ := hl
      refine ⟨a, ?_, rfl⟩
      show π (ψ a) = 0
      funext j
      exact h0 j.1 j.2
  choose d hd using key
  refine ⟨d, hd, ?_⟩
  choose u huL hu0 hud using fun i => (hd i (d i)).1 (Ideal.mem_span_singleton_self _)
  let X : Matrix (Fin n) (Fin n) R := Matrix.of fun j i => u i j
  have hcol : ∀ i, u i ∈ LinearMap.range X.mulVecLin := fun i =>
    ⟨Pi.single i 1, by ext j; simp [X]⟩
  have hrange : LinearMap.range X.mulVecLin = L := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      have : X.mulVecLin a = ∑ i, a i • u i := by
        ext j
        simp [X, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [this]
      exact L.sum_mem fun i _ => L.smul_mem _ (huL i)
    · have hind : ∀ t : ℕ, ∀ l ∈ L, (∀ j : Fin n, (j : ℕ) + t < n → l j = 0) →
          l ∈ LinearMap.range X.mulVecLin := by
        intro t
        induction t with
        | zero =>
          intro l _ h0
          have : l = 0 := funext fun j => h0 j (by simp)
          rw [this]
          exact Submodule.zero_mem _
        | succ t ih =>
          intro l hl h0
          by_cases ht : t < n
          · let i : Fin n := ⟨n - 1 - t, by omega⟩
            have hi : (i : ℕ) = n - 1 - t := rfl
            have hlow : ∀ j, j < i → l j = 0 := fun j hj => h0 j (by
              have := Fin.lt_def.1 hj
              omega)
            obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ((hd i (l i)).2 ⟨l, hl, hlow, rfl⟩)
            have h3 := ih (l - c • u i) (L.sub_mem hl (L.smul_mem _ (huL i))) (fun j hj => by
              rcases lt_or_eq_of_le (show j ≤ i from Fin.le_def.2 (by omega)) with h | h
              · simp [hlow j h, hu0 i j h]
              · subst h
                simp [hud, hc])
            have h4 := Submodule.add_mem _ h3 (Submodule.smul_mem _ c (hcol i))
            simpa using h4
          · exact ih l hl fun j hj => by omega
      intro l hl
      exact hind n l hl fun j hj => by omega
  have hdet : X.det = ∏ i, d i := by
    rw [Matrix.det_of_lowerTriangular X (fun j i h => hu0 i j h)]
    exact Finset.prod_congr rfl fun i _ => hud i
  have := Smith.hasLen_coker_det hv X
  rw [hrange, hdet, map_prod, map_prod] at this
  exact this

end PositivityTheory.HtPt.Rb
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RhPull
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

theorem sub_pull : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K := by
  intro p C _ R _ _ N N' _ _ M M' j K hM hG g hg
  rw [← hM] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  have hinv : g' ∈ invFun M' ⊥ := ⟨hg', fun x k hk => by rw [AddSubgroup.mem_bot.1 hk, add_zero]⟩
  have h1 : g' ∈ Algebra.adjoin R ((afFun p (invFun M' ⊥) : Submodule R (N' → C)) : Set (N' → C)) :=
    hG hinv
  change (fun x => g' (j x)) ∈
    Algebra.adjoin R ((afFun p (invFun M K) : Submodule R (N → C)) : Set (N → C))
  clear hg' hinv
  induction h1 using Algebra.adjoin_induction with
  | mem f hf =>
    refine Algebra.subset_adjoin ⟨?_, fun x y => ?_⟩
    · rw [← hM]
      exact ⟨f, hf.1.1, rfl⟩
    · have := hf.2 (j x) (j y)
      simpa only [map_add (f := _)] using this
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add f f' _ _ h h' => exact Subalgebra.add_mem _ h h'
  | mul f f' _ _ h h' => exact Subalgebra.mul_mem _ h h'

end PositivityTheory.HtPt.Rh
end

