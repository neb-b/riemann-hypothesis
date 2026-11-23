module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPreservesLadicDecayDividedPower
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.Decay

theorem pow_add_mul_range {M R : Type} [AddCommGroup M] [CommRing R] (f : M →+ R)
    (hm : ∀ x y : M, ∃ z, f z = f x * f y) (x y : M) (c n : ℕ) :
    ∃ p g : M, f p = f x ^ (n + 1) ∧ (f x + c * f y) ^ (n + 1) = f x ^ (n + 1) + c * f g := by
  induction n with
  | zero => exact ⟨x, y, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨p, g, hp, hg⟩ := ih
    obtain ⟨p', hp'⟩ := hm p x
    obtain ⟨z1, h1⟩ := hm p y
    obtain ⟨z2, h2⟩ := hm g x
    obtain ⟨z3, h3⟩ := hm g y
    refine ⟨p', z1 + z2 + c • z3, by rw [hp', hp]; ring, ?_⟩
    rw [pow_succ, hg, map_add (f := _), map_add (f := _), map_nsmul, h1, h2, h3, hp, nsmul_eq_mul]
    ring

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

def ofWHom : (ℕ × ℕ → Wq l a) →+ (ZMod a → K⟦X⟧⟦X⟧) :=
  AddMonoidHom.mk' (ofW t K e) fun x y => by
    funext τ
    ext i n
    simp only [Pi.add_apply, map_add (f := _), coeff_ofW, add_div]

theorem ofWHom_apply (w : ℕ × ℕ → Wq l a) : ofWHom t K e w = ofW t K e w := rfl

theorem eq_zero_of_coeff [CharZero K]
    (hinj : ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c))
    (w : ℕ × ℕ → Wq l a) (i n : ℕ) (h : coeff n (coeff i (ofW t K e w 0)) = 0) : w (i, n) = 0 := by
  rw [coeff_ofW, div_eq_zero_iff] at h
  have h2 : (dpDen e i n : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos e i n).ne'
  apply hinj 0
  simpa using h.resolve_right h2

theorem ofWHom_injective [CharZero K]
    (hinj : ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c)) :
    Function.Injective (ofWHom t K e) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro w hw
  funext ⟨i, n⟩
  apply eq_zero_of_coeff t K e hinj
  rw [← ofWHom_apply, hw]
  simp

theorem box_cofinite (M : ℕ) : ∀ᶠ p : ℕ × ℕ in cofinite, M < p.1 ∨ M < p.2 := by
  rw [Filter.eventually_cofinite]
  refine ((Set.finite_Iic M).prod (Set.finite_Iic M)).subset ?_
  rintro ⟨i, n⟩ h
  simp only [Set.mem_setOf_eq, not_or, not_lt] at h
  exact h

end GlobalTheory.CrysPrism.Decay

namespace GlobalTheory.CrysPrism
open Decay

theorem frob_keeps_decay (l : ℕ) [hl : Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hinj : ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c))
    (hmul : ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e)
    (hQ : ∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂)
    (hsupp : ∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) →
      ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n →
        coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0)
    (w : ℕ × ℕ → Wq l a) (hw : LTo0 l w) (v b : ℕ × ℕ → Wq l a)
    (hv : frob2 φ₂ (ofW t K e w) = ofW t K e v)
    (hb : frob2 φ₂ (ofW t K e w) = ofW t K e w ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e b) :
    LTo0 l v ∧ LTo0 l b := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := natCast_ne_zero_ps (natCast_ne_zero_ps hl0)
  have hI := ofWHom_injective t K e hinj
  have key : ∀ r : ℕ, ∀ᶠ p in cofinite, (l : Wq l a) ^ r ∣ v p ∧ (l : Wq l a) ^ r ∣ b p := by
    intro r
    have hS := hw (r + 1)
    rw [Filter.eventually_cofinite] at hS
    obtain ⟨⟨N1, N2⟩, hN⟩ := hS.bddAbove
    let w1 : ℕ × ℕ → Wq l a := fun p => if (l : Wq l a) ^ (r + 1) ∣ w p then 0 else w p
    have hex : ∀ p, ∃ c, w p = w1 p + (l ^ (r + 1) : ℕ) • c := by
      intro p
      by_cases h : (l : Wq l a) ^ (r + 1) ∣ w p
      · obtain ⟨c, hc⟩ := id h
        refine ⟨c, ?_⟩
        simp only [w1, if_pos h]
        simp [hc]
      · exact ⟨0, by simp only [w1, if_neg h]; simp⟩
    choose w2 hw2 using hex
    have hw12 : w = w1 + (l ^ (r + 1) : ℕ) • w2 := funext hw2
    have hw1 : ∀ i n, max N1 N2 < i ∨ max N1 N2 < n → w1 (i, n) = 0 := by
      intro i n h
      by_cases h' : (l : Wq l a) ^ (r + 1) ∣ w (i, n)
      · simp only [w1, if_pos h']
      · have h3 : (i, n) ≤ (N1, N2) := hN h'
        obtain ⟨h4, h5⟩ := h3
        simp only at h4 h5
        omega
    obtain ⟨M, hM⟩ := hsupp _ w1 hw1
    obtain ⟨-, ⟨v1, hv1⟩, _, ⟨b1, rfl⟩, hb1⟩ := hQ _ ⟨w1, rfl⟩
    obtain ⟨-, ⟨v2, hv2⟩, -⟩ := hQ _ ⟨w2, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := Nat.exists_eq_succ_of_ne_zero hl.out.ne_zero
    obtain ⟨-, g, -, hg⟩ := pow_add_mul_range (ofWHom t K e)
      (fun x y => hmul _ ⟨x, rfl⟩ _ ⟨y, rfl⟩) w1 w2 (l ^ (r + 1)) k
    rw [← hk] at hg
    have hF : ofW t K e w = ofW t K e w1 + ((l ^ (r + 1) : ℕ) : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e w2 := by
      rw [← ofWHom_apply, hw12, map_add (f := _), map_nsmul, nsmul_eq_mul]; rfl
    have hφ : frob2 φ₂ (ofW t K e w) =
        ofW t K e v1 + ((l ^ (r + 1) : ℕ) : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e v2 := by
      rw [hF, map_add (f := _), map_mul, map_natCast, hv1, hv2]
    have e1 : v = v1 + (l ^ (r + 1) : ℕ) • v2 := by
      apply hI
      rw [map_add (f := _), map_nsmul, nsmul_eq_mul, ofWHom_apply, ← hv, hφ]; rfl
    have e2 : b = b1 + (l ^ r : ℕ) • (v2 - g) := by
      apply hI
      rw [map_add (f := _), map_nsmul, map_sub, nsmul_eq_mul, ← sub_eq_zero]
      apply tf_pi hl2
      simp only [ofWHom_apply] at hg ⊢
      rw [← hF] at hg
      rw [← hv1] at hb1
      push_cast at hg hφ ⊢
      linear_combination hφ - hb - hg + hb1
    filter_upwards [box_cofinite M] with ⟨i, n⟩ hp
    obtain ⟨m1, m2⟩ := hM 0 i n hp
    have z1 : v1 (i, n) = 0 := eq_zero_of_coeff t K e hinj v1 i n (by rw [hv1]; exact m1)
    have z2 : b1 (i, n) = 0 := by
      apply eq_zero_of_coeff t K e hinj
      rw [hb1, ← nsmul_eq_mul, Pi.add_apply, map_add (f := _), map_add (f := _), m2, zero_add, Pi.smul_apply, map_nsmul, map_nsmul,
        nsmul_eq_mul] at m1
      exact (mul_eq_zero.1 m1).resolve_left hl0
    constructor
    · rw [e1]
      simp only [Pi.add_apply, Pi.smul_apply, z1, zero_add, nsmul_eq_mul, Nat.cast_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (Nat.le_succ r)) _
    · rw [e2]
      simp only [Pi.add_apply, Pi.smul_apply, z2, zero_add, nsmul_eq_mul, Nat.cast_pow]
      exact Dvd.intro _ rfl
  exact ⟨fun r => (key r).mono fun _ h => h.1, fun r => (key r).mono fun _ h => h.2⟩

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvari
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLqPerm

theorem isChar_one {G : Type} [Group G] : IsChar (fun _ : G => (1 : ℂ)) := by
  refine ⟨FDRep.of (Representation.trivial ℂ G ℂ), fun x => ?_⟩
  change LinearMap.trace ℂ ℂ ((Representation.trivial ℂ G ℂ) x) = 1
  simp [Representation.trivial, LinearMap.trace_id]

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

variable {g : ℕ} [Fact g.Prime]

theorem isChar_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) : IsChar (hcL L (degL L)) := by
  induction L with
  | nil => exact isChar_one
  | cons p L ih =>
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    rw [hcL_cons]
    exact ((_root_.GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp g p.1 (degL L) (degL (p :: L)) hdeg).1 p.2 (hcL L (degL L))
      (hL p (by simp)) (ih fun q hq => hL q (by simp [hq])))

theorem degL_perm {L L' : List (Pc g)} (h : L.Perm L') : degL L = degL L' := by
  unfold degL
  exact (h.map _).sum_eq

theorem hc_congr_mid (a : ℕ) (α : Gn g a → ℂ) (F : (m : ℕ) → Gn g m → ℂ) (n m m' : ℕ) (h : m = m') :
    hc a m α (F m) n = hc a m' α (F m') n := by subst h; rfl

theorem hc_congr_left (c : ℕ) (γ : Gn g c → ℂ) (F : (m : ℕ) → Gn g m → ℂ) (n m m' : ℕ) (h : m = m') :
    hc m c (F m) γ n = hc m' c (F m') γ n := by subst h; rfl

theorem hcL_perm {L L' : List (Pc g)} (h : L.Perm L') :
    (∀ p ∈ L, IsChar p.2) → ∀ n, n = degL L → hcL L n = hcL L' n := by
  induction h with
  | nil => intro _ n _; rfl
  | cons x h ih =>
    rename_i L₁ L₂
    intro hc1 n hn
    rw [hcL_cons, hcL_cons, ih (fun q hq => hc1 q (by simp [hq])) _ rfl]
    exact hc_congr_mid x.1 x.2 (hcL L₂) n _ _ (degL_perm h)
  | swap x y L₁ =>
    intro hc1 n hn
    have hx : IsClass x.2 := isClass_of_isChar (hc1 x (by simp))
    have hy : IsClass y.2 := isClass_of_isChar (hc1 y (by simp))
    have hL : IsClass (hcL L₁ (degL L₁)) :=
      isClass_of_isChar (isChar_hcL L₁ fun q hq => hc1 q (by simp [hq]))
    have hn' : n = y.1 + x.1 + degL L₁ := by rw [hn]; simp [degL]; omega
    have hn'' : n = x.1 + y.1 + degL L₁ := by rw [hn']; omega
    have e1 : degL (x :: L₁) = x.1 + degL L₁ := by simp [degL]
    have e2 : degL (y :: L₁) = y.1 + degL L₁ := by simp [degL]
    simp only [hcL_cons]
    rw [hc_congr_mid y.1 y.2 (fun m => hc x.1 (degL L₁) x.2 (hcL L₁ (degL L₁)) m) n _ _ e1,
      hc_congr_mid x.1 x.2 (fun m => hc y.1 (degL L₁) y.2 (hcL L₁ (degL L₁)) m) n _ _ e2]
    rw [← (_root_.GlobalTheory.GLq.HcRing.main g y.1 x.1 (degL L₁) n y.2 x.2 _ hy hx hL).1 hn',
      ← (_root_.GlobalTheory.GLq.HcRing.main g x.1 y.1 (degL L₁) n x.2 y.2 _ hx hy hL).1 hn'',
      (_root_.GlobalTheory.GLq.HcRing.main g y.1 x.1 (degL L₁) (y.1 + x.1) y.2 x.2 _ hy hx hL).2.1 rfl]
    exact hc_congr_left (degL L₁) (hcL L₁ (degL L₁)) (fun m => hc x.1 y.1 x.2 y.2 m) n _ _ (Nat.add_comm _ _)
  | trans h₁ h₂ ih₁ ih₂ =>
    intro hc1 n hn
    rw [ih₁ hc1 n hn, ih₂ (fun q hq => hc1 q (h₁.mem_iff.mpr hq)) n (hn.trans (degL_perm h₁))]

end GlobalTheory.GLqPerm

theorem GlobalTheory.gl_list_product_perm_char : ∀ (g : ℕ) [Fact g.Prime] (L L' : List (Pc g)) (n : ℕ), n = degL L → (∀ p ∈ L, IsChar p.2) → IsChar (hcL L n) ∧ (L.Perm L' → hcL L n = hcL L' n) := by
  intro g _ L L' n hn hL
  subst hn
  exact ⟨GlobalTheory.GLqPerm.isChar_hcL L hL, fun h => GlobalTheory.GLqPerm.hcL_perm h hL _ rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionTwoBlockCuspidalEqZero
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem list_sum_posNat {ι : Type} (L : List ι) (f : ι → ℂ) (hf : ∀ p ∈ L, ∃ n : ℕ, 0 < n ∧ f p = n) :
    ∃ m : ℕ, (L.map f).sum = m ∧ (L ≠ [] → 0 < m) := by
  induction L with
  | nil => exact ⟨0, by simp, fun h => absurd rfl h⟩
  | cons p L ih =>
    obtain ⟨n, hn, hp⟩ := hf p (List.mem_cons_self ..)
    obtain ⟨m, hm, -⟩ := ih fun q hq => hf q (List.mem_cons_of_mem _ hq)
    refine ⟨n + m, ?_, fun _ => by omega⟩
    simp [List.map_cons, List.sum_cons, hp, hm]

theorem res_cusp_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (d a : ℕ) (χ : Gn g d → ℂ), IsCusp χ → 0 < a → a < d →
    ∀ x y, res a (d - a) χ x y = 0 := by
  intro g _ d a χ hχ ha had x y
  obtain ⟨-, hirr, hc⟩ := hχ
  have hchar : IsChar χ := by
    obtain ⟨V, -, hV⟩ := hirr
    exact ⟨V, hV⟩
  obtain ⟨L, hL, hres⟩ := (_root_.GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp g a (d - a) d (by omega)).2 χ hchar
  have hpos : ∀ p ∈ L, ∃ n : ℕ, 0 < n ∧ (fun p : (Gn g a → ℂ) × (Gn g (d - a) → ℂ) => p.1 1 * p.2 1) p = n := by
    intro p hp
    obtain ⟨d₁, hd₁, h₁⟩ := (_root_.GlobalTheory.GLq.trIdem (Gn g a) 0 p.1).2.1 (hL p hp).1
    obtain ⟨d₂, hd₂, h₂⟩ := (_root_.GlobalTheory.GLq.trIdem (Gn g (d - a)) 0 p.2).2.1 (hL p hp).2
    exact ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, by simp [h₁, h₂]⟩
  obtain ⟨m, hm, hmpos⟩ := list_sum_posNat L _ hpos
  have hL0 : L = [] := by
    by_contra hne
    have h0 : res a (d - a) χ 1 1 = 0 := hc a ha had
    rw [hres, hm] at h0
    have := hmpos hne
    exact absurd (by exact_mod_cast h0 : m = 0) (by omega)
  rw [hres, hL0]
  simp

end GlobalTheory.GLq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfRationalIntegrality
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LatTied

theorem latStable_tied : ∀ (D : D7) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M) (Q : D.what₂.places.Pl → Finset (PlE D.host)),
    (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) →
    ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → GlobalTheory.EtaJoin.LatStable Tn.B j w := by
  intro D M Tn Q hQ hI j w h1 h2 hw
  classical
  by_cases hne : (D.nd.locs j w).Nonempty
  · obtain ⟨i, hi⟩ := hne
    have hwi : D.nd.w i = w := ((D.nd.locs_mem j w i).1 hi).2
    have hQc : Tn.B.Qc j w = Q w := by rw [← Tn.Q_eq j w i hi, hQ i, hwi]
    apply _root_.GlobalTheory.LatStab.latStable_of_latInt D M Tn.B j h1 h2 w
    rw [hQc]; exact hI j h1 h2 w hw
  · have hsub : Subsingleton (heckeAlg Tn.B j w) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      obtain ⟨I, hI'⟩ := Ideal.exists_maximal (heckeAlg Tn.B j w)
      obtain ⟨i, hi, -⟩ := Tn.mx_all j w h1 h2 hw I hI'
      exact hne ⟨i, hi⟩
    have h10 : (1 : Module.End (FractionRing (Tn.B.Oc j w)) (Tn.B.V j w)) = 0 := by
      have := congrArg Subtype.val (Subsingleton.elim (1 : heckeAlg Tn.B j w) 0)
      simpa using this
    have hx : ∀ y : Tn.B.V j w, y = 0 := fun y => by
      have := LinearMap.congr_fun h10 y
      simpa using this
    intro v k _ x _
    rw [hx (Tn.B.hK j w v k x)]
    exact Submodule.zero_mem _

end GlobalTheory.LatTied

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageDeRhamEqEisensteinPowMulOfComponents
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem iotaO_toOB (C : GlobalTheory.MemLoc.Core l) (x : OCr l O) :
    iotaO O C (toOB l O x) = dRO l O (crisToOD l O x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w =>
    exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y)
      ((C.ι_j w).trans (by rw [eq_crisP C.j_cris]; rfl))
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem iotaO_iSl {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (g : invL l (S O K e)) :
    iotaO O C (ϖ.iSl O K g) = dRO l O (ϖ.iSD O K g) := by
  have h : (iotaO O C).toRingHom.comp (ϖ.iSl O K).toRingHom = (dRO l O).toRingHom.comp (ϖ.iSD O K) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (l : S O K e)) (RingHom.ext fun s => ?_)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    have h3 : ϖ.iSl O K (algebraMap (S O K e) (invL l (S O K e)) s) = toOB l O (ϖ.iS O K s) :=
      ϖ.iSl_of_mem O K s.2 _
    have h4 : ϖ.iSD O K (algebraMap (S O K e) (invL l (S O K e)) s) = crisToOD l O (ϖ.iS O K s) :=
      ϖ.iSD_of_mem O K s.2 _
    rw [h3, h4]
    exact iotaO_toOB C _
  exact RingHom.congr_fun h g

end GlobalTheory.BKGal.HatVal


open GlobalTheory.BKGal.HatVal in
theorem GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) [CompleteSpace K] (C : GlobalTheory.MemLoc.Core l) (η : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, ∃ r ∈ Rpi O K l e, (f τ : K⟦X⟧) = E K l e ^ η * r) → ∃ z : OD l O, iotaO O C (ϖ.iB t K f) = dRO l O (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ η * z) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ C η f hf
  choose r hr hfr using hf
  set P : OD l O := toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) with hP
  have hE : ϖ.iHat O K (Ehat O K l e) = P := by
    rw [Ehat, PiSys.iHat_ofAl]
    exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
  have hS : ∀ τ, ϖ.iSD O K (f τ) = P ^ η * ϖ.iHat O K (toHat O K l e ⟨r τ, hr τ⟩) := fun τ => by
    have h1 : hat O l e ((f τ : invL l (S O K e)) : K⟦X⟧) =
        algebraMap _ (AhatE O K l e) (Ehat O K l e ^ η * toHat O K l e ⟨r τ, hr τ⟩) := by
      have h2 : E K l e ^ η * r τ = ((EIn l e (Rpi O K l e) ^ η * ⟨r τ, hr τ⟩ : Rpi O K l e) : K⟦X⟧) := by
        simp [EIn]
      rw [hfr τ, h2, hat_coe_Rpi, map_mul, map_pow, toHat_E]
    rw [GlobalTheory.BKReal.TwoMaps.iSD_eq_iHat_of_hat l a e O K t ϖ (f τ) _ h1, map_mul, map_pow, hE]
  refine ⟨∑ τ, idem (constD t) τ * ϖ.iHat O K (toHat O K l e ⟨r τ, hr τ⟩), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PiSys.iB, glue_apply, map_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hI : iotaO O C (idem (constB t) τ) = dRO l O (idem (constD t) τ) :=
    iotaO_toB C (constA t (Pi.single τ 1))
  rw [map_mul, hI, iotaO_iSl ϖ C (f τ), hS, map_mul, map_mul, map_mul]
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteDividedPowerSeriesSubringPrime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem GlobalTheory.CrysPrism.isAdicComplete_Sd : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), IsAdicComplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  exact GlobalTheory.CrysPrism.Compl.isAdicComplete_of t e (_root_.GlobalTheory.CrysPrism.sdSet_closed l a e O K t)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition

noncomputable section

namespace GlobalTheory.Pass.LocDual

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def locU {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  GlobalTheory.JumpDual.matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (Br.loc D.nbr i w hw M)
    (GlobalTheory.JumpDual.loc_cont D i w hw M hM)

def IsSummandTw (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)) : Prop :=
  ∃ (a : ℕ) (x : Fin a → ↥Xs) (j : X.V →ₗ[Br.LL D.nbr i w hw] (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw)),
    Function.Injective j ∧
    (∀ g v, j (X.ρ g v) = fun b => (Br.loc D.nbr i w hw (rTwO D.nd i r (x b)) g).mulVec (j v b)) ∧
    ∃ C : Submodule (Br.LL D.nbr i w hw) (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw),
      (∀ g, ∀ u ∈ C, (fun b => (Br.loc D.nbr i w hw (rTwO D.nd i r (x b)) g).mulVec (u b)) ∈ C) ∧
      IsCompl (LinearMap.range j) C

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL]

def DualLatLe (U U' : GRep G Qp LL O) (LT : Lattice (O := O) U.ρ) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL) (b : ℕ) : Prop :=
  ∃ LT' : Lattice (O := O) U'.ρ, IsDualLat1 PD LT LT' P ∧ finrank O ↥(latticeFiniteCohomology PD LT') + finrank O ↥LT.T ≤ b

end Gen

end GlobalTheory.Pass.LocDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedAtOfIsUnramifiedInGaloisExtensionStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedAt_of_isUnramifiedInGaloisExtension : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)}, GlobalTheory.NT.UnramIn L 𝔭 → ∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver 𝔭.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) P := by
  first | exact @GlobalTheory.NT.isUnramifiedAt_of_unramIn | exact GlobalTheory.NT.isUnramifiedAt_of_unramIn | (intros; apply GlobalTheory.NT.isUnramifiedAt_of_unramIn <;> assumption)
end

