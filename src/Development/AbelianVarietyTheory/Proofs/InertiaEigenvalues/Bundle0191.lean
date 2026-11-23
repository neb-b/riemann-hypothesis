module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0184
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0186

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeTwistExactSequenceCohomology
section
noncomputable section

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory.TensIsoExt

open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)

section Abstract

variable {O G : Type} [CommRing O] [Group G]
variable {A B C : Type} [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
  [AddCommGroup C] [Module O C]

def ambMap {π : Representation O G A} {π' : Representation O G B} (f : A →ₗ[O] B)
    (hf : ∀ g m, f (π g m) = π' g (f m)) : Amb π →ₗ[O] Amb π' :=
  Submodule.mapQ _ _ (f.compLeft G) (by
    rintro z ⟨b, -, hb⟩
    refine ⟨f b, Submodule.mem_top, ?_⟩
    funext g
    have h1 : π g b - b = z g := congrFun hb g
    change π' g (f b) - f b = f (z g)
    rw [← h1, map_sub, hf])

theorem ambMap_mk {π : Representation O G A} {π' : Representation O G B} (f : A →ₗ[O] B)
    (hf : ∀ g m, f (π g m) = π' g (f m)) (u : G → A) :
    ambMap f hf (Submodule.Quotient.mk u) = Submodule.Quotient.mk (fun g => f (u g)) := rfl

theorem amb_eq_iff {π : Representation O G A} (u v : G → A) :
    (Submodule.Quotient.mk u : Amb π) = Submodule.Quotient.mk v ↔ ∃ m, ∀ g, π g m - m = u g - v g := by
  rw [Submodule.Quotient.eq, ReciprocityTheory.Def.B1, Submodule.mem_map]
  constructor
  · rintro ⟨m, -, hm⟩
    exact ⟨m, fun g => congrFun hm g⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, Submodule.mem_top, funext hm⟩

variable [TopologicalSpace G]

theorem mem_range_toAmb {π : Representation O G A} (x : Amb π) :
    x ∈ LinearMap.range (toAmb π) ↔ ∃ z ∈ Z1 π ⊤, Submodule.Quotient.mk z = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Submodule.Quotient.mk ⟨z, hz⟩, rfl⟩

theorem mem_cocycles_units_iff {π : Representation O G A} (z : G → A) :
    z ∈ Z1 π ⊤ ↔ IsLocallyConstant z ∧ ∀ g h, π g (z h) - z (g * h) + z g = 0 := by
  rw [Z1, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨hc, hd⟩
    exact ⟨hc.1, fun g h => congrFun hd (g, h)⟩
  · rintro ⟨hlc, hd⟩
    refine ⟨⟨hlc, fun _ => Submodule.mem_top⟩, ?_⟩
    funext x
    exact hd x.1 x.2

variable {HA HB HC : Type} [AddCommGroup HA] [Module O HA] [AddCommGroup HB] [Module O HB]
  [AddCommGroup HC] [Module O HC]

private theorem ambMap_injective_lemma {πA : Representation O G A} {πB : Representation O G B}
    {πC : Representation O G C} (α : A →ₗ[O] B) (β : B →ₗ[O] C) (hα : ∀ g m, α (πA g m) = πB g (α m))
    (hβ : ∀ g m, β (πB g m) = πC g (β m)) (αinj : Function.Injective α) (ex : Function.Exact α β)
    (hinv : πC.invariants = ⊥) : Function.Injective (ambMap α hα) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h0 : (Submodule.Quotient.mk (fun g => α (u g)) : Amb πB) = Submodule.Quotient.mk 0 := by
    rw [Submodule.Quotient.mk_zero, ← hx, ambMap_mk]
  obtain ⟨m, hm⟩ := (amb_eq_iff _ _).1 h0
  have hm' : ∀ g, πB g m - m = α (u g) := fun g => by simpa using hm g
  have hfix : β m ∈ πC.invariants := by
    rw [Representation.mem_invariants]
    intro g
    have e := congrArg β (hm' g)
    rw [map_sub, hβ, ex.apply_apply_eq_zero] at e
    exact sub_eq_zero.1 e
  rw [hinv, Submodule.mem_bot] at hfix
  obtain ⟨a₀, ha₀⟩ := (ex m).1 hfix
  rw [← Submodule.Quotient.mk_zero, amb_eq_iff]
  refine ⟨a₀, fun g => αinj ?_⟩
  rw [map_sub, hα, ha₀, hm' g, Pi.zero_apply, sub_zero]

theorem five {πA : Representation O G A} {πB : Representation O G B} {πC : Representation O G C}
    (α : A →ₗ[O] B) (β : B →ₗ[O] C) (hα : ∀ g m, α (πA g m) = πB g (α m))
    (hβ : ∀ g m, β (πB g m) = πC g (β m)) (αinj : Function.Injective α) (ex : Function.Exact α β)
    (βsurj : Function.Surjective β)
    (a : HA →ₗ[O] HB) (b : HB →ₗ[O] HC) (ex' : Function.Exact a b) (bsurj : Function.Surjective b)
    (φA : HA →ₗ[O] Amb πA) (φB : HB →ₗ[O] Amb πB) (φC : HC →ₗ[O] Amb πC)
    (sqa : ∀ y, ambMap α hα (φA y) = φB (a y)) (sqb : ∀ y, ambMap β hβ (φB y) = φC (b y))
    (hle : LinearMap.range φB ≤ LinearMap.range (toAmb πB))
    (hlc : ∀ m, IsLocallyConstant fun g => πB g m) (hinv : πC.invariants = ⊥)
    (hA : Function.Injective φA ∧ LinearMap.range φA = LinearMap.range (toAmb πA))
    (hC : Function.Injective φC ∧ LinearMap.range φC = LinearMap.range (toAmb πC)) :
    Function.Injective φB ∧ LinearMap.range φB = LinearMap.range (toAmb πB) := by
  have hαi := ambMap_injective_lemma α β hα hβ αinj ex hinv
  refine ⟨?_, le_antisymm hle ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : φC (b y) = 0 := by rw [← sqb, hy, map_zero]
    have h2 : b y = 0 := hC.1 (by rw [h1, map_zero])
    obtain ⟨x, rfl⟩ := (ex' y).1 h2
    have h3 : φA x = 0 := hαi (by rw [sqa, hy, map_zero])
    have h4 : x = 0 := hA.1 (by rw [h3, map_zero])
    rw [h4, map_zero]
  · rintro _ ⟨ζ, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ ζ
    obtain ⟨hzlc, hzc⟩ := (mem_cocycles_units_iff (z : G → B)).1 z.2
    have hβz : (fun g => β ((z : G → B) g)) ∈ Z1 πC ⊤ := by
      refine (mem_cocycles_units_iff _).2 ⟨hzlc.comp β, fun g h => ?_⟩
      rw [← hβ, ← map_sub, ← map_add (f := _), hzc g h, map_zero]
    have hC' := (mem_range_toAmb (Submodule.Quotient.mk (fun g => β ((z : G → B) g)) : Amb πC)).2
      ⟨_, hβz, rfl⟩
    rw [← hC.2] at hC'
    obtain ⟨w, hw⟩ := hC'
    obtain ⟨y, rfl⟩ := bsurj w
    obtain ⟨z', hz'mem, hz'eq⟩ := (mem_range_toAmb (φB y)).1 (hle (LinearMap.mem_range_self φB y))
    obtain ⟨hz'lc, hz'c⟩ := (mem_cocycles_units_iff z').1 hz'mem
    have hcl : (Submodule.Quotient.mk (fun g => β (z' g)) : Amb πC) =
        Submodule.Quotient.mk (fun g => β ((z : G → B) g)) := by
      rw [← ambMap_mk β hβ, hz'eq, sqb, hw]
    obtain ⟨c, hc⟩ := (amb_eq_iff _ _).1 hcl
    obtain ⟨m₀, hm₀⟩ := βsurj c
    have hk : ∀ g, β ((z : G → B) g - z' g + (πB g m₀ - m₀)) = 0 := by
      intro g
      have e := hc g
      rw [map_add (f := _), map_sub, map_sub, hβ, hm₀, e]
      abel
    choose u hu using fun g => (ex ((z : G → B) g - z' g + (πB g m₀ - m₀))).1 (hk g)
    have hulc : IsLocallyConstant u := by
      refine IsLocallyConstant.desc u α ?_ αinj
      have e : α ∘ u = fun g => (z : G → B) g - z' g + (πB g m₀ - m₀) := funext hu
      rw [e]
      exact (hzlc.sub hz'lc).add ((hlc m₀).sub (IsLocallyConstant.const m₀))
    have hum : u ∈ Z1 πA ⊤ := by
      refine (mem_cocycles_units_iff u).2 ⟨hulc, fun g h => αinj ?_⟩
      have e1 : (z : G → B) (g * h) = πB g ((z : G → B) h) + (z : G → B) g := by
        have e := hzc g h
        rw [sub_add_eq_add_sub, sub_eq_zero] at e
        exact e.symm
      have e2 : z' (g * h) = πB g (z' h) + z' g := by
        have e := hz'c g h
        rw [sub_add_eq_add_sub, sub_eq_zero] at e
        exact e.symm
      rw [map_zero, map_add (f := _), map_sub, hα, hu, hu, hu, e1, e2, map_mul, Module.End.mul_apply]
      simp only [map_add (f := _), map_sub]
      abel
    obtain ⟨x, hx⟩ : Submodule.Quotient.mk u ∈ LinearMap.range φA := by
      rw [hA.2]
      exact (mem_range_toAmb _).2 ⟨u, hum, rfl⟩
    refine ⟨y + a x, ?_⟩
    rw [map_add (f := _), ← sqa, hx, ambMap_mk, ← hz'eq, ← Submodule.Quotient.mk_add]
    change _ = (Submodule.Quotient.mk (z : G → B) : Amb πB)
    rw [amb_eq_iff]
    refine ⟨m₀, fun g => ?_⟩
    rw [Pi.add_apply, hu]
    abel

end Abstract
section Tens

variable {G LL O V : Type} [Group G] [TopologicalSpace G] [Field LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousConstSMul LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (χ : G →* Oˣ)
  {X X' : Type} [AddCommGroup X] [Module O X] [AddCommGroup X'] [Module O X']


omit [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] in
theorem lTensor_equivariant (f : X →ₗ[O] X') (g : G) (m : ↥L.T ⊗[O] X) :
    f.lTensor ↥L.T (twCoef (latRep L) χ X g m) = twCoef (latRep L) χ X' g (f.lTensor ↥L.T m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul t x => simp only [twCoef, coefRep_tmul, LinearMap.lTensor_tmul]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem tensAmb_natural (f : X →ₗ[O] X') (y : H1tw L χ ⊗[O] X) :
    ambMap (f.lTensor ↥L.T) (lTensor_equivariant L χ f) (tensAmb L χ X y) =
      tensAmb L χ X' (f.lTensor (H1tw L χ) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x =>
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [LinearMap.lTensor_tmul, tensAmb_tmul, tensAmb_tmul, ambMap_mk]
    congr 1
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

end Tens

theorem tensIso_of_exact : ∀ (G LL O V : Type) [Group G] [TopologicalSpace G] [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V) (L : Lattice (O := O) ρ) (χ : G →* Oˣ) (S X Y : Type) [AddCommGroup S] [Module O S] [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (i : S →ₗ[O] X) (p : X →ₗ[O] Y), Function.Injective i → Function.Exact i p → Function.Surjective p → (∀ c x, tensCoc L χ X c x ∈ ReciprocityTheory.Def.Z1 (twCoef (latRep L) χ X) ⊤) → (∀ m, IsLocallyConstant fun g => twCoef (latRep L) χ X g m) → (twCoef (latRep L) χ Y).invariants = ⊥ → TensIso L χ S → TensIso L χ Y → TensIso L χ X := by
  intro G LL O V _ _ _ _ _ _ _ _ _ _ _ _ ρ L χ S X Y _ _ _ _ _ _ i p hi hex hp hcoc hlc hinv hS hY
  have := L.free
  refine five (i.lTensor ↥L.T) (p.lTensor ↥L.T) (lTensor_equivariant L χ i) (lTensor_equivariant L χ p)
    (Module.Flat.lTensor_preserves_injective_linearMap i hi) (lTensor_exact _ hex hp)
    (LinearMap.lTensor_surjective _ hp) (i.lTensor (H1tw L χ)) (p.lTensor (H1tw L χ))
    (lTensor_exact _ hex hp) (LinearMap.lTensor_surjective _ hp)
    (tensAmb L χ S) (tensAmb L χ X) (tensAmb L χ Y) (fun y => tensAmb_natural L χ i y)
    (fun y => tensAmb_natural L χ p y) ?_ hlc hinv hS hY
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul c x =>
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [tensAmb_tmul]
    exact (mem_range_toAmb _).2 ⟨_, hcoc c x, rfl⟩
  | add p q hp hq => rw [map_add (f := _)]; exact Submodule.add_mem _ hp hq

end GlobalTheory.TensIsoExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LaurentCoeffNegEqZeroOfBounded
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

namespace GlobalTheory

theorem norm_eTwoPi_I_mul (y : ℝ) : ‖eTwoPi (Complex.I * y)‖ = Real.exp (-(2 * Real.pi * y)) := by
  rw [eTwoPi, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem laurent_coeff_neg_eq_zero_of_bounded : ∀ (F : ℂ⸨X⸩) (T C : ℝ),
    (∀ w : ℂ, T < w.im → ∃ x : ℂ, HasSum (fun m : ℤ => F.coeff m * eTwoPi w ^ m) x ∧ ‖x‖ ≤ C) →
    ∀ m : ℤ, m < 0 → F.coeff m = 0 := by
  intro F T C h m hm
  by_contra hne
  have hF : F ≠ 0 := by rintro rfl; exact hne (by simp)
  have hm₀le : F.order ≤ m := by
    by_contra hlt; push_neg at hlt; exact hne (HahnSeries.coeff_eq_zero_of_lt_order hlt)
  have hc : F.coeff F.order ≠ 0 := fun h0 => hF (HahnSeries.coeff_order_eq_zero.1 h0)
  obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat (le_of_lt (lt_of_le_of_lt hm₀le hm))
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
  set m₀ := F.order with hm₀
  set y₁ : ℝ := max T 0 + 1 with hy₁
  have hy₁T : T < y₁ := by have := le_max_left T 0; linarith
  have hy₁0 : 0 < y₁ := by have := le_max_right T 0; linarith
  obtain ⟨x₁, hx₁, -⟩ := h (Complex.I * y₁) (by simpa using hy₁T)
  set q₁ := eTwoPi (Complex.I * y₁) with hq₁
  set ρ₁ := ‖q₁‖ with hρ₁
  have hρ₁pos : 0 < ρ₁ := by rw [hρ₁, hq₁, norm_eTwoPi_I_mul]; exact Real.exp_pos _
  have hS : Summable (fun m : ℤ => ‖F.coeff m * q₁ ^ m‖) := hx₁.summable.norm
  set S := ∑' m : ℤ, ‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k with hSdef
  have key : ∀ y : ℝ, y₁ ≤ y →
      ‖F.coeff m₀‖ ≤ C * Real.exp (-(2 * Real.pi * y)) ^ k + Real.exp (-(2 * Real.pi * y)) / ρ₁ * S := by
    intro y hy
    obtain ⟨x, hx, hxC⟩ := h (Complex.I * y) (by simpa using lt_of_lt_of_le hy₁T hy)
    set q := eTwoPi (Complex.I * y) with hq
    set ρ := ‖q‖ with hρ
    have hρe : ρ = Real.exp (-(2 * Real.pi * y)) := norm_eTwoPi_I_mul y
    have hq0 : q ≠ 0 := Complex.exp_ne_zero _
    have hρle : ρ ≤ ρ₁ := by
      rw [hρe, hρ₁, hq₁, norm_eTwoPi_I_mul, Real.exp_le_exp]
      nlinarith [Real.pi_pos]
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    set r : ℤ → ℂ := fun m => F.coeff m * q ^ m * q ^ k - (if m = m₀ then F.coeff m₀ else 0) with hr
    have h2 : HasSum r (x * q ^ k - F.coeff m₀) := (hx.mul_right (q ^ k)).sub (hasSum_ite_eq m₀ _)
    have hbd : ∀ m, ‖r m‖ ≤ ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k) := by
      intro m
      have hRnn : 0 ≤ ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k) := by positivity
      by_cases hmm : m = m₀
      · subst hmm
        have : q ^ m₀ * q ^ k = 1 := by
          rw [hk, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hq0)]
        have : r m₀ = 0 := by simp only [hr, mul_assoc, this, mul_one]; simp
        rw [this, norm_zero]; exact hRnn
      rcases lt_or_gt_of_ne hmm with hlt | hgt
      · have : r m = 0 := by simp only [hr, if_neg hmm, HahnSeries.coeff_eq_zero_of_lt_order hlt, zero_mul, sub_zero]
        rw [this, norm_zero]; exact hRnn
      · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show (0:ℤ) ≤ m - m₀ - 1 by omega)
        have hm : m = (n + 1 : ℕ) - (k : ℤ) := by push_cast; omega
        have e1 : ∀ t : ℝ, t ≠ 0 → t ^ m * t ^ k = t ^ (n + 1) := fun t ht => by
          rw [← zpow_natCast t k, ← zpow_add₀ ht, ← zpow_natCast]; congr 1; omega
        have hρpos : 0 < ρ := by rw [hρe]; exact Real.exp_pos _
        have hrm : ‖r m‖ = ‖F.coeff m‖ * (ρ ^ m * ρ ^ k) := by
          simp only [hr, if_neg hmm, sub_zero, norm_mul, norm_pow, norm_zpow, ← hρ, mul_assoc]
        have hq₁m : ‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k = ‖F.coeff m‖ * (ρ₁ ^ m * ρ₁ ^ k) := by
          rw [norm_mul, norm_zpow, ← hρ₁, mul_assoc]
        rw [hrm, hq₁m, e1 ρ hρpos.ne', e1 ρ₁ hρ₁pos.ne']
        have hpow : ρ ^ n ≤ ρ₁ ^ n := pow_le_pow_left₀ hρ0 hρle n
        have hc0 : 0 ≤ ‖F.coeff m‖ := norm_nonneg _
        rw [pow_succ, pow_succ]
        calc ‖F.coeff m‖ * (ρ ^ n * ρ) ≤ ‖F.coeff m‖ * (ρ₁ ^ n * ρ) := by gcongr
          _ = ρ / ρ₁ * (‖F.coeff m‖ * (ρ₁ ^ n * ρ₁)) := by field_simp
    have hg : HasSum (fun m => ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k)) (ρ / ρ₁ * S) :=
      (hS.mul_right (ρ₁ ^ k)).hasSum.mul_left _
    have h3 : ‖x * q ^ k - F.coeff m₀‖ ≤ ρ / ρ₁ * S := by
      rw [← h2.tsum_eq]; exact tsum_of_norm_bounded hg hbd
    have h4 : ‖x * q ^ k‖ ≤ C * ρ ^ k := by
      rw [norm_mul, norm_pow]; exact mul_le_mul_of_nonneg_right hxC (by positivity)
    rw [← hρe]
    calc ‖F.coeff m₀‖ = ‖x * q ^ k - (x * q ^ k - F.coeff m₀)‖ := by ring_nf
      _ ≤ ‖x * q ^ k‖ + ‖x * q ^ k - F.coeff m₀‖ := norm_sub_le _ _
      _ ≤ C * ρ ^ k + ρ / ρ₁ * S := add_le_add h4 h3
  have hlim : Filter.Tendsto (fun y : ℝ => Real.exp (-(2 * Real.pi * y))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp
      (Filter.tendsto_id.const_mul_atTop (by positivity)))
  have hlim2 : Filter.Tendsto (fun y : ℝ => C * Real.exp (-(2 * Real.pi * y)) ^ k +
      Real.exp (-(2 * Real.pi * y)) / ρ₁ * S) Filter.atTop (nhds 0) := by
    have := ((hlim.pow k).const_mul C).add ((hlim.div_const ρ₁).mul_const S)
    simpa [zero_pow hk0] using this
  have hle : ‖F.coeff m₀‖ ≤ 0 :=
    ge_of_tendsto hlim2 (Filter.eventually_atTop.2 ⟨y₁, key⟩)
  exact hc (norm_le_zero_iff.1 hle)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemEisensteinFiltrationEqEisensteinPowMulDiscStatement
section
open PowerSeries Filter Topology GlobalTheory.BK GlobalTheory.FilDiv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_eisensteinFiltration_eq_eisenstein_pow_mul_disc : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (j : ℕ), ∀ φ : S O K e, φ ∈ Fil O K l e j → ∃ q ∈ Rpi (O := O) (K := K) l e, (φ : K⟦X⟧) = E K l e ^ j * q := by
  intro O K _ _ _ _ _ _ l e _ _ _ j φ hφ
  have filPre_divisible : ∀ {g : S O K e}, g ∈ FilPre O K l e j →
      ∃ q ∈ Rpi (O := O) (K := K) l e, (g : K⟦X⟧) = E K l e ^ j * q := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, hx⟩ := hx
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi
      refine ⟨C (((m + j).factorial : K)⁻¹) * E K l e ^ m,
        mul_mem (HasK.C_mem _) (pow_mem (E_mem l e _) m), ?_⟩
      rw [hx, Ediv]; ring
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨q, hq, h⟩ := hx
      obtain ⟨q', hq', h'⟩ := hy
      exact ⟨q + q', add_mem hq hq', by rw [Subalgebra.coe_add, h, h', mul_add]⟩
    | smul c x _ hx =>
      obtain ⟨q, hq, h⟩ := hx
      exact ⟨c * q, mul_mem (S_le_R l e c.2) hq, by
        rw [smul_eq_mul, Subalgebra.coe_mul, h]; ring⟩
  have divisible_of_approximation : ∀ (j : ℕ) {ψ : K⟦X⟧}, ψ ∈ Rpi (O := O) (K := K) l e →
      (∀ n : ℕ, ∃ q ∈ Rpi (O := O) (K := K) l e,
        ∀ k, ‖coeff k (ψ - E K l e ^ j * q)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n) →
      ∃ q ∈ Rpi (O := O) (K := K) l e, ψ = E K l e ^ j * q := by
    intro j ψ hψ H
    induction j generalizing ψ with
    | zero => exact ⟨ψ, hψ, by simp⟩
    | succ j ih =>
      have hQ := quotE_mem_Rpi l e hψ
      have key : ∀ n, ∃ q ∈ Rpi (O := O) (K := K) l e,
          (∀ k, ‖coeff k (quotE l e ψ - E K l e ^ j * q)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n) ∧
          ∀ k, ‖coeff k (ψ - E K l e * quotE l e ψ)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1) := by
        intro n
        obtain ⟨q, hq, hr⟩ := H (n + 1)
        have hrR : ψ - E K l e ^ (j + 1) * q ∈ Rpi (O := O) (K := K) l e :=
          sub_mem hψ (mul_mem (pow_mem (E_mem l e _) _) hq)
        generalize hr_def : ψ - E K l e ^ (j + 1) * q = r at hr hrR
        have hg : quotE l e ψ - E K l e ^ j * q - quotE l e r = 0 := by
          refine eq_zero_of_E_mul l e (sub_mem (sub_mem hQ (mul_mem (pow_mem (E_mem l e _) _) hq))
            (quotE_mem_Rpi l e hrR)) fun m => ?_
          have h1 := coeff_sub_E_mul_quotE l e hψ m
          have h2 := coeff_sub_E_mul_quotE l e hrR m
          have : E K l e * (quotE l e ψ - E K l e ^ j * q - quotE l e r) =
              (r - E K l e * quotE l e r) - (ψ - E K l e * quotE l e ψ) := by
            rw [← hr_def]; ring
          rw [this, map_sub, h1, h2, sub_zero]
        have hg' : quotE l e ψ - E K l e ^ j * q = quotE l e r := sub_eq_zero.1 hg
        have hrem : ψ - E K l e * quotE l e ψ = r - E K l e * quotE l e r := by
          rw [← hg', ← hr_def]; ring
        exact ⟨q, hq, fun k => by rw [hg']; exact norm_coeff_quotE_le l e hr k,
          fun k => by rw [hrem]; exact norm_coeff_rem_le l e hr k⟩
      choose qs hqs hsmall hrem using key
      obtain ⟨q, hq, hQ'⟩ := ih hQ fun n => ⟨qs n, hqs n, hsmall n⟩
      have hR0 : ψ - E K l e * quotE l e ψ = 0 := by
        ext k
        rw [map_zero]
        have hρ := pow_pos (rad_pos l (1 / (e : ℝ))) k
        have ht : Tendsto (fun n : ℕ => ‖(l : K)‖ ^ (n + 1)) atTop (𝓝 0) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one l)).comp
            (tendsto_add_atTop_nat 1)
        have h0 : ‖coeff k (ψ - E K l e * quotE l e ψ)‖ * rad l (1 / e) ^ k ≤ 0 :=
          ge_of_tendsto' ht fun n => hrem n k
        exact norm_le_zero_iff.1 (le_of_mul_le_mul_right (by simpa using h0) hρ)
      refine ⟨q, hq, ?_⟩
      rw [sub_eq_zero] at hR0
      rw [hR0, hQ', pow_succ']; ring
  have hψ : (φ : K⟦X⟧) ∈ Rpi (O := O) (K := K) l e := S_le_R l e φ.2
  refine divisible_of_approximation j hψ fun n => ?_
  obtain ⟨g, hg, h, H⟩ := (mem_Fil l).1 hφ n
  obtain ⟨q, hq, hgq⟩ := filPre_divisible hg
  refine ⟨q, hq, fun k => ?_⟩
  have : (φ : K⟦X⟧) - E K l e ^ j * q = (l : K⟦X⟧) ^ n * h := by
    rw [H]; push_cast; rw [hgq]; ring
  rw [this]
  exact norm_coeff_pow_mul_le l e n h.2 k
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUntiltSubEqOneOfPowFixed
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.TiltAbs

theorem norm_untilt_sub_eq_one_of_pow_fixed :
    ∀ (l : ℕ) [Fact l.Prime] (o : ℕ) (ζ ζ' : Formalism.Per.Fl l), 0 < o → ζ ^ (l ^ o) = ζ →
      ζ' ^ (l ^ o) = ζ' → ζ ≠ ζ' → ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 := by
  intro l _ o ζ ζ' ho h1 h2 hne
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  set d : Formalism.Per.Fl l := ζ - ζ' with hd
  have hdpow : d ^ (l ^ o) = d := by
    rw [hd, sub_pow_char_pow, h1, h2]
  have hd0 : d ≠ 0 := sub_ne_zero.2 hne
  set a : ℝ := ‖((d.untilt : Formalism.Per.OC l) : ℂ_[l])‖ with ha
  have ha0 : a ≠ 0 := by
    intro h
    apply hd0
    refine (untilt_ultrametric_definite l d 0).2 ?_
    have : ((d.untilt : Formalism.Per.OC l) : ℂ_[l]) = 0 := norm_eq_zero.1 h
    exact Subtype.ext this
  have hapow : a ^ (l ^ o) = a := by
    have := congrArg (fun x : Formalism.Per.Fl l => ‖((x.untilt : Formalism.Per.OC l) : ℂ_[l])‖) hdpow
    simp only [map_pow, SubmonoidClass.coe_pow, norm_pow] at this
    exact this
  have hlo : 1 ≤ l ^ o := Nat.one_le_pow _ _ (by omega)
  have hlo' : l ^ o - 1 ≠ 0 := by
    have : 1 < l ^ o := Nat.one_lt_pow (by omega) hl
    omega
  have hsub : a ^ (l ^ o - 1) = 1 := by
    have : a ^ (l ^ o - 1) * a = 1 * a := by
      rw [← pow_succ, Nat.sub_add_cancel hlo, hapow, one_mul]
    exact mul_right_cancel₀ ha0 this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hlo').1 hsub

end GlobalTheory.TiltAbs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitClassTrivial
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory

theorem orbit_class_trivial : ∀ (o : ℕ) (p : ℝ) (f : ℕ → ℝ → ℝ), 0 < o → 1 < p → (∀ i, ContinuousOn (f i) (Set.Ioc 0 1)) → (∀ i, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ f i r) → (∀ i j, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 < f i r → 0 < f j r → i % o = j % o) → (∀ r ∈ Set.Ioc (0 : ℝ) 1, ∃ i, 0 < f i r) → (∀ i r, 0 < r → r ≤ 1 / p → 0 < f i r → 0 < f (i + 1) (p * r)) → o = 1 := by
  intro o p f _ho hp hc _ hcl hcov hsh
  classical
  let g : ℝ → ℕ := fun r => if h : ∃ i, 0 < f i r then (Classical.choose h) % o else 0
  have hg : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i, 0 < f i r → g r = i % o := by
    intro r hr i hi
    have h : ∃ i, 0 < f i r := ⟨i, hi⟩
    simp only [g, dif_pos h]
    exact hcl _ _ r hr (Classical.choose_spec h) hi
  have gcont : ContinuousOn g (Set.Ioc (0 : ℝ) 1) := by
    intro r hr
    obtain ⟨i, hi⟩ := hcov r hr
    rw [ContinuousWithinAt, nhds_discrete, Filter.tendsto_pure]
    have h1 : ∀ᶠ x in nhdsWithin r (Set.Ioc (0 : ℝ) 1), 0 < f i x :=
      ((hc i) r hr).eventually (lt_mem_nhds hi)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxs
    rw [hg x hxs i hx, hg r hr i hi]
  have hp0 : 0 < p := by linarith
  have hr1 : 1 / p ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hp0]; exact hp.le⟩
  have h1 : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨one_pos, le_rfl⟩
  have hconst : g (1 / p) = g 1 := isPreconnected_Ioc.constant gcont hr1 h1
  obtain ⟨i, hi⟩ := hcov (1 / p) hr1
  have hi1 : 0 < f (i + 1) 1 := by
    have := hsh i (1 / p) (by positivity) le_rfl hi
    rwa [mul_one_div_cancel hp0.ne'] at this
  have hmod : (i + 1) % o = (i + 0) % o := by
    rw [add_zero, ← hg _ hr1 i hi, ← hg _ h1 (i + 1) hi1, hconst]
  have h10 : 1 ≡ 0 [MOD o] := Nat.ModEq.add_left_cancel' i hmod
  exact Nat.dvd_one.mp (Nat.modEq_zero_iff_dvd.mp h10)

end GlobalTheory
end

