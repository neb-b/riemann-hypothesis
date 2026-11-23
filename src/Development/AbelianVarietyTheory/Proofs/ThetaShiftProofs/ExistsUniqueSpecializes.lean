module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Specialise

open GlobalTheory.Points GlobalTheory.AmpleSpan

section Coords

variable {A : Type} [CommRing A] {X Y : Scheme.{0}} {H : LB X} {ι : Type*} {t : ι → LB.Sec H}
  {x : Sp A ⟶ X} {c : ι → A}

def HasCoords (x : Sp A ⟶ X) (t : ι → LB.Sec H) (c : ι → A) : Prop :=
  ∃ k, ⊤ ≤ x ⁻¹ᵁ H.U k ∧ ∃ u : Aˣ, ∀ l, valR x (H.U k) ((t l).f k) = c l * u

theorem le_preimage_inf (x : Sp A ⟶ X) {U V : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) := fun _ hz => ⟨hU hz, hV hz⟩

theorem valR_compat (s : LB.Sec H) (x : Sp A ⟶ X) {j k : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j) (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valR x (H.U j) (s.f j) = valR x (H.U j ⊓ H.U k) (H.g j k).val * valR x (H.U k) (s.f k) := by
  have h := le_preimage_inf x hj hk
  have e := congrArg (valR x (H.U j ⊓ H.U k)) (s.compat j k)
  rwa [valR_mul x _ h, valR_res x _ h, valR_res x _ h] at e

theorem HasCoords.chart (h : HasCoords x t c) {j : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j) :
    ∃ u : Aˣ, ∀ l, valR x (H.U j) ((t l).f j) = c l * u := by
  obtain ⟨k, hk, u, hu⟩ := h
  have hg : IsUnit (valR x (H.U j ⊓ H.U k) (H.g j k).val) := by
    rw [valR_eq x _ (le_preimage_inf x hj hk)]
    exact (Units.isUnit _).map _
  refine ⟨hg.unit * u, fun l => ?_⟩
  rw [valR_compat (t l) x hj hk, hu, Units.val_mul, IsUnit.unit_spec, mul_left_comm]

theorem HasCoords.mul_unit (h : HasCoords x t c) {a : A} (ha : IsUnit a) : HasCoords x t fun l => c l * a := by
  obtain ⟨k, hk, u, hu⟩ := h
  obtain ⟨a, rfl⟩ := ha
  exact ⟨k, hk, a⁻¹ * u, fun l => by rw [hu, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]⟩

theorem HasCoords.le_nonzeroLocus (h : HasCoords x t c) {l : ι} (hl : IsUnit (c l)) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (t l) := by
  obtain ⟨k, hk, u, hu⟩ := h
  refine le_preimage_mono x (le_iSup (fun k => X.basicOpen ((t l).f k)) k) ?_
  rw [le_preimage_basicOpen_iff x hk, hu]
  exact hl.mul u.isUnit

theorem valR_isRatio {s s₀ : LB.Sec H} {ρ : Γ(X, nonzeroLocus s₀)} (hρ : IsRatio s s₀ ρ) (x : Sp A ⟶ X)
    (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus s₀) {k : H.ι} (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valR x (H.U k) (s.f k) = valR x (nonzeroLocus s₀) ρ * valR x (H.U k) (s₀.f k) := by
  have h := le_preimage_inf x hx hk
  have e := congrArg (valR x (nonzeroLocus s₀ ⊓ H.U k)) (hρ k)
  rwa [valR_mul x _ h, valR_res x _ h, valR_res x _ h, valR_res x _ h] at e

theorem HasCoords.valR_ratio (h : HasCoords x t c) {l m : ι} (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (t m))
    {ρ : Γ(X, nonzeroLocus (t m))} (hρ : IsRatio (t l) (t m) ρ) : valR x (nonzeroLocus (t m)) ρ * c m = c l := by
  obtain ⟨k, hk, u, hu⟩ := h
  have e := valR_isRatio hρ x hx hk
  rw [hu, hu, ← mul_assoc] at e
  exact (u.mul_left_inj.1 e).symm

theorem exists_chart_isUnit [IsLocalRing A] {s : LB.Sec H} (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus s) :
    ∃ k, ⊤ ≤ x ⁻¹ᵁ H.U k ∧ IsUnit (valR x (H.U k) (s.f k)) := by
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 ((le_preimage_iff x _).1 hx)
  have hk' := (le_preimage_iff x _).2 hk
  have hU := le_preimage_mono x (X.basicOpen_le _) hk'
  exact ⟨k, hU, (le_preimage_basicOpen_iff x hU _).1 hk'⟩

theorem HasCoords.le_nonzeroLocus_iff [IsLocalRing A] (h : HasCoords x t c) (l : ι) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (t l) ↔ IsUnit (c l) := by
  refine ⟨fun hx => ?_, h.le_nonzeroLocus⟩
  obtain ⟨k, hk, hu⟩ := exists_chart_isUnit hx
  obtain ⟨u, e⟩ := h.chart hk
  rw [e] at hu
  exact isUnit_of_mul_isUnit_left hu

theorem HasCoords.exists_isUnit [IsLocalRing A] (h : HasCoords x t c) (hcov : ⨆ l, nonzeroLocus (t l) = ⊤) :
    ∃ l, IsUnit (c l) := by
  obtain ⟨l, hl⟩ := exists_le_preimage_of_iSup_eq_top x hcov
  exact ⟨l, (h.le_nonzeroLocus_iff l).1 hl⟩

theorem hasCoords_ratio [IsLocalRing A] {m : ι} (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (t m))
    {ρ : ι → Γ(X, nonzeroLocus (t m))} (hρ : ∀ l, IsRatio (t l) (t m) (ρ l)) :
    HasCoords x t fun l => valR x (nonzeroLocus (t m)) (ρ l) := by
  obtain ⟨k, hk, hu⟩ := exists_chart_isUnit hx
  exact ⟨k, hk, hu.unit, fun l => valR_isRatio (hρ l) x hx hk⟩

theorem valR_eval₂Hom (f : X ⟶ Y) (x : Sp A ⟶ X) {U : X.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ U) (ρ : ι → Γ(X, U))
    (q : MvPolynomial ι Γ(Y, ⊤)) :
    valR x U (MvPolynomial.eval₂Hom (f.appLE ⊤ U le_top).hom ρ q) =
      MvPolynomial.eval₂Hom (valMap (x ≫ f) ⊤ (le_preimage_top _)).hom (fun l => valR x U (ρ l)) q := by
  rw [valR_eq x U hx, MvPolynomial.map_eval₂Hom, ← appLE_valMap x f (U := ⊤) le_top hx]
  simp only [valR_eq x U hx]
  rfl

end Coords

section Embedded

variable {A : Type} [CommRing A] {X Y : Scheme.{0}} {f : X ⟶ Y} {H : LB X} {ι : Type} {t : ι → LB.Sec H}

theorem HasCoords.ext (ht : EmbedsBy f t) {x x' : Sp A ⟶ X} (hf : x ≫ f = x' ≫ f) {c : ι → A}
    (h : HasCoords x t c) (h' : HasCoords x' t c) {m : ι} (hm : IsUnit (c m)) : x = x' := by
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hx := h.le_nonzeroLocus hm
  have hx' := h'.le_nonzeroLocus hm
  refine ext_of_valR hD hx hx' fun g => ?_
  obtain ⟨q, rfl⟩ := hsurj g
  rw [valR_eval₂Hom f x hx, valR_eval₂Hom f x' hx']
  have e : (fun l => valR x _ (ρ l)) = fun l => valR x' _ (ρ l) := funext fun l =>
    hm.mul_right_cancel ((h.valR_ratio hx (hρ l)).trans (h'.valR_ratio hx' (hρ l)).symm)
  rw [e]
  simp only [hf]

theorem HasCoords.ext_of_isLocalRing [IsLocalRing A] (ht : EmbedsBy f t) {x x' : Sp A ⟶ X} (hf : x ≫ f = x' ≫ f)
    {c : ι → A} (h : HasCoords x t c) (h' : HasCoords x' t c) : x = x' := by
  obtain ⟨m, hm⟩ := h.exists_isUnit ht.1
  exact h.ext ht hf h' hm

variable {K : Type} [Field K] {j : A →+* K}

theorem isDominant_spMap (hj : Function.Injective j) : IsDominant (spMap j) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩

theorem ext_of_spMap_comp [IsSeparated f] (hj : Function.Injective j) {ξ ξ' : Sp A ⟶ X} (hf : ξ ≫ f = ξ' ≫ f)
    (h : spMap j ≫ ξ = spMap j ≫ ξ') : ξ = ξ' := by
  have := isDominant_spMap hj
  have : IsDomain A := hj.isDomain j
  exact ext_of_isDominant_of_isSeparated f hf (spMap j) h

theorem exists_lift_of_valR_mem (hj : Function.Injective j) {D : X.Opens} (hD : IsAffineOpen D) (x : Sp K ⟶ X)
    (hx : ⊤ ≤ x ⁻¹ᵁ D) (h : ∀ g, valR x D g ∈ j.range) :
    ∃ ξ : Sp A ⟶ X, ⊤ ≤ ξ ⁻¹ᵁ D ∧ spMap j ≫ ξ = x := by
  choose φ hφ using h
  simp only [valR_eq x D hx] at hφ
  let ψ : Γ(X, D) →+* A := ⟨⟨⟨φ, hj (by simp [hφ])⟩, fun a b => hj (by simp [hφ])⟩, hj (by simp [hφ]),
    fun a b => hj (by simp [hφ])⟩
  refine ⟨_, le_preimage_specMap_fromSpec hD (CommRingCat.ofHom ψ), ?_⟩
  rw [← specMap_valMap_fromSpec hD x hx, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext hφ)

theorem exists_lift [Y.IsSeparated] (ht : EmbedsBy f t) (hj : Function.Injective j) {b : Sp A ⟶ Y} {x : Sp K ⟶ X}
    (hb : x ≫ f = spMap j ≫ b) {c : ι → A} (h : HasCoords x t fun l => j (c l)) {m : ι} (hm : IsUnit (c m)) :
    ∃ ξ : Sp A ⟶ X, ⊤ ≤ ξ ⁻¹ᵁ nonzeroLocus (t m) ∧ ξ ≫ f = b ∧ spMap j ≫ ξ = x := by
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hx := h.le_nonzeroLocus (hm.map j)
  obtain ⟨ξ, hξ, e⟩ := exists_lift_of_valR_mem hj hD x hx fun g => by
    obtain ⟨q, rfl⟩ := hsurj g
    rw [valR_eval₂Hom f x hx]
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C, ← valR_eq, hb, valR_spMap_comp j b ⊤ (le_preimage_top _)]
      exact ⟨_, rfl⟩
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p l hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      refine mul_mem hp ⟨c l * hm.unit⁻¹.val, (hm.map j).mul_right_cancel ?_⟩
      rw [h.valR_ratio hx (hρ l), ← map_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]
  refine ⟨ξ, hξ, ext_of_spMap_comp (f := terminal.from Y) hj (terminal.hom_ext _ _) ?_, e⟩
  rw [← Category.assoc, e, hb]

end Embedded

section Rings

variable {R K C : Type} [CommRing R] [Field K] [Field C] {i : R →+* K}

instance ker_isPrime (ev : R →+* C) : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev

end Rings

section Relation

variable {R K C : Type} [CommRing R] [Field K] [Field C] {i : R →+* K} {X S : Scheme.{0}}

variable {hi : Function.Injective i} {ev : R →+* C} {p : X ⟶ S} {b : Sp R ⟶ S} {x : Sp K ⟶ X} {y : Sp C ⟶ X}

end Relation

section Existence

variable {R K C : Type} [CommRing R] [Field K] [Field C] {i : R →+* K} {X S : Scheme.{0}} {p : X ⟶ S}
  {H : LB X} {ι : Type} {t : ι → LB.Sec H} {b : Sp R ⟶ S} {x : Sp K ⟶ X} {r : ι → R}

end Existence

section Group

open MonObj

variable {R K C : Type} [CommRing R] [Field K] [Field C] {i : R →+* K} {S : Scheme.{0}} {A : Over S}
  {hi : Function.Injective i} {ev : R →+* C} {b : Sp R ⟶ S} {sK : Sp K ⟶ S} {sC : Sp C ⟶ S}

end Group

end GlobalTheory.Specialise
