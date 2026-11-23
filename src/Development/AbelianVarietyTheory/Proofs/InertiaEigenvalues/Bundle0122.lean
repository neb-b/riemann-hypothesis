module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0107
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountAndGramDetSignNormClass
section
noncomputable section

namespace GlobalTheory.UnitLemma.NormClass

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial

section Orb

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

def mulLatEquiv (u : Aˣ) : Submodule O A ≃ Submodule O A where
  toFun := mulLat O (u : A)
  invFun := mulLat O ((u⁻¹ : Aˣ) : A)
  left_inv L := by
    ext y
    simp only [mem_mulLat, inv_inv, Units.inv_mul_cancel_left]
  right_inv L := by
    ext y
    simp only [mem_mulLat, inv_inv, Units.mul_inv_cancel_left]

end Orb

variable {K : UQ}

open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
private theorem isLat_mulLat_unit {E : Type} [Field E] [Algebra E A] (u : Aˣ) (L : Submodule O A)
    (hL : _root_.GlobalTheory.UnitLemma.IsLat O E L) : _root_.GlobalTheory.UnitLemma.IsLat O E (_root_.GlobalTheory.UnitLemma.mulLat O (u : A) L) := by
  unfold _root_.GlobalTheory.UnitLemma.IsLat at hL ⊢
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.mulLat
    exact hL.1.map _
  · unfold _root_.GlobalTheory.UnitLemma.mulLat
    rw [Submodule.map_coe]
    have e : (⇑(LinearMap.mulLeft O (u : A))) = ⇑(LinearMap.mulLeft E (u : A)) := rfl
    rw [e, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
    intro z
    exact ⟨((u⁻¹ : Aˣ) : A) * z, by simp⟩

open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
private theorem forall_mem_mulLat_unit_iff (u : Aˣ) (L : Submodule O A) (P : A → Prop) :
    (∀ z ∈ _root_.GlobalTheory.UnitLemma.mulLat O (u : A) L, P z) ↔ ∀ z ∈ L, P (u * z) := by
  constructor
  · intro h z hz
    exact h _ ((_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat u L _).mpr (by rwa [Units.inv_mul_cancel_left]))
  · intro h z hz
    have := h _ ((_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat u L z).mp hz)
    rwa [Units.mul_inv_cancel_left] at this

open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in
private theorem herm_mul_unit_sigma (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ) (a b : B.A) :
    B.herm (x * (u * B.σ (u : B.A))) a b = B.herm x (u * a) (u * b) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  simp only [map_mul]
  congr 1
  ring

open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in
private theorem mem_X_mul_unit_sigma_iff (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ)
    (L : Submodule K.O B.A) :
    L ∈ B.X (x * (u * B.σ (u : B.A))) ↔ _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L ∈ B.X x := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.X
  simp only [Set.mem_setOf_eq]
  refine and_congr ?_ (and_congr ?_ ?_)
  · refine ⟨isLat_mulLat_unit u L, fun h => ?_⟩
    have := isLat_mulLat_unit (u⁻¹) _ h
    have hL : _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) (_root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L) = L :=
      (_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).left_inv L
    rwa [hL] at this
  · rw [forall_mem_mulLat_unit_iff]
    constructor
    · intro h z hz
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, mul_left_comm, Units.inv_mul_cancel_left]
      exact h z hz
    · intro h z hz
      have := h z hz
      rwa [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, mul_left_comm, Units.inv_mul_cancel_left] at this
  · constructor
    · intro h w
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, h, forall_mem_mulLat_unit_iff]
      simp only [herm_mul_unit_sigma, Units.mul_inv_cancel_left]
    · intro h w
      have := h (u * w)
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, Units.inv_mul_cancel_left, forall_mem_mulLat_unit_iff] at this
      rw [this]
      simp only [herm_mul_unit_sigma]

open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
private theorem mulLat_unit_comm (u t : Aˣ) (L : Submodule O A) :
    _root_.GlobalTheory.UnitLemma.mulLat O (u : A) (_root_.GlobalTheory.UnitLemma.mulLat O (t : A) L) =
      _root_.GlobalTheory.UnitLemma.mulLat O (t : A) (_root_.GlobalTheory.UnitLemma.mulLat O (u : A) L) := by
  ext y
  simp only [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat]
  rw [mul_left_comm]


open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in
theorem _root_.GlobalTheory.UnitLemma.NormClass.N_norm_class : ∀ (K : _root_.GlobalTheory.UnitLemma.UQ) (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ),
    B.N (x * (u * B.σ (u : B.A))) = B.N x ∧
      K.eta (B.gramDet (x * (u * B.σ (u : B.A)))) = K.eta (B.gramDet x) := by
  intro K B x u
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.InvAlg.N _root_.GlobalTheory.UnitLemma.orbSum
    simp only [one_mul]
    let wt : Submodule K.O B.A → ℚ := fun L =>
      ((_root_.GlobalTheory.UnitLemma.stabLat K.O L ⊓ B.T).relIndex (_root_.GlobalTheory.UnitLemma.intUnits K.O B.A ⊓ B.T) : ℚ)
    have hwt : ∀ (t : B.Aˣ) (L : Submodule K.O B.A), wt (_root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) = wt L := by
      intro t L
      simp only [wt, _root_.GlobalTheory.UnitLemma.Orbit.stabLat_mulLat]
    have hrel : ∀ (X : Set (Submodule K.O B.A)) (a b : X),
        (∃ t ∈ B.T, (b : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) a) → wt a = wt b := by
      rintro X a b ⟨t, -, h⟩
      rw [h, hwt]
    have hout : ∀ (X : Set (Submodule K.O B.A)) (o : Quot (fun L M : X => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L)),
        wt ((Quot.out o : X) : Submodule K.O B.A) = Quot.lift (fun a : X => wt a) (hrel X) o := by
      intro X o
      conv_rhs => rw [← Quot.out_eq o]
    show (∑ᶠ o : Quot (fun L M : B.X (x * (u * B.σ (u : B.A))) => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L), wt ((Quot.out o : B.X (x * (u * B.σ (u : B.A)))) : Submodule K.O B.A)) =
      ∑ᶠ o : Quot (fun L M : B.X x => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L), wt ((Quot.out o : B.X x) : Submodule K.O B.A)
    simp only [hout]
    have hφ : ∀ L : B.X (x * (u * B.σ (u : B.A))), _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L ∈ B.X x :=
      fun L => (mem_X_mul_unit_sigma_iff B x u L).mp L.2
    have hψ : ∀ M : B.X x, _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) M ∈ B.X (x * (u * B.σ (u : B.A))) := by
      intro M
      refine (mem_X_mul_unit_sigma_iff B x u _).mpr ?_
      have hM : _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) (_root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) M) = M :=
        (_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).right_inv (M : Submodule K.O B.A)
      rw [hM]
      exact M.2
    let e : Quot (fun L M : B.X (x * (u * B.σ (u : B.A))) => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) ≃
        Quot (fun L M : B.X x => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) :=
      { toFun := Quot.map (fun L => ⟨_, hφ L⟩) (by
          rintro a b ⟨t, ht, h⟩
          refine ⟨t, ht, ?_⟩
          show _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) b = _
          rw [h]
          exact mulLat_unit_comm u t (a : Submodule K.O B.A))
        invFun := Quot.map (fun M => ⟨_, hψ M⟩) (by
          rintro a b ⟨t, ht, h⟩
          refine ⟨t, ht, ?_⟩
          show _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) b = _
          rw [h]
          exact mulLat_unit_comm u⁻¹ t (a : Submodule K.O B.A))
        left_inv := by
          intro o
          induction o using Quot.ind with
          | mk L => exact congrArg (Quot.mk _) (Subtype.ext ((_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).left_inv (L : Submodule K.O B.A)))
        right_inv := by
          intro o
          induction o using Quot.ind with
          | mk M => exact congrArg (Quot.mk _) (Subtype.ext ((_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).right_inv (M : Submodule K.O B.A))) }
    rw [← finsum_comp_equiv e]
    refine finsum_congr fun o => ?_
    induction o using Quot.ind with
    | mk L => exact (hwt u (L : Submodule K.O B.A)).symm
  · let φ : B.A ≃ₗ[K.E] B.A :=
      { LinearMap.mulLeft K.E (u : B.A) with
        invFun := fun z => ((u⁻¹ : B.Aˣ) : B.A) * z
        left_inv := fun z => Units.inv_mul_cancel_left u z
        right_inv := fun z => Units.mul_inv_cancel_left u z }
    have e : B.gramDet (x * (u * B.σ (u : B.A))) =
        (Matrix.of fun i j => B.herm x (((Module.finBasis K.E B.A).map φ) i)
          (((Module.finBasis K.E B.A).map φ) j)).det := by
      unfold _root_.GlobalTheory.UnitLemma.InvAlg.gramDet
      simp only [herm_mul_unit_sigma, Module.Basis.map_apply]
      rfl
    rw [e, _root_.GlobalTheory.UnitLemma.Orbit.eta_gram]

end GlobalTheory.UnitLemma.NormClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSatMOfSmul
section
namespace GlobalTheory.NL.Coker

open Formalism.BasicNotions

variable {O : Type} [CommRing O] {n : ℕ} {M : Type} [AddCommGroup M] [Module (LetA O n) M]

def satM (p : ℕ) (P N : Submodule (LetA O n) M) : Submodule (LetA O n) M where
  carrier := {x | x ∈ N ∧ ∃ k : ℕ, ((p : LetA O n)) ^ k • x ∈ P ∧ (letπ : LetA O n) ^ k • x ∈ P}
  add_mem' := by
    rintro x y ⟨hx, k, hk1, hk2⟩ ⟨hy, j, hj1, hj2⟩
    refine ⟨N.add_mem hx hy, k + j, ?_, ?_⟩
    · rw [smul_add, pow_add]
      refine P.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact P.smul_mem _ hk1
      · rw [mul_smul]; exact P.smul_mem _ hj1
    · rw [smul_add, pow_add]
      refine P.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact P.smul_mem _ hk2
      · rw [mul_smul]; exact P.smul_mem _ hj2
  zero_mem' := ⟨N.zero_mem, 0, by simp, by simp⟩
  smul_mem' := by
    rintro a x ⟨hx, k, hk1, hk2⟩
    refine ⟨N.smul_mem a hx, k, ?_, ?_⟩
    · rw [smul_comm]; exact P.smul_mem a hk1
    · rw [smul_comm]; exact P.smul_mem a hk2

theorem satM_le (p : ℕ) (P N : Submodule (LetA O n) M) : satM p P N ≤ N := fun _ hx => hx.1

theorem le_satM (p : ℕ) {P N : Submodule (LetA O n) M} (h : P ≤ N) : P ≤ satM p P N :=
  fun x hx => ⟨h hx, 0, by simpa using hx, by simpa using hx⟩

theorem mem_satM_of_smul {p : ℕ} {P N : Submodule (LetA O n) M} {x : M} (hx : x ∈ N)
    (h1 : ((p : LetA O n)) • x ∈ satM p P N) (h2 : (letπ : LetA O n) • x ∈ satM p P N) :
    x ∈ satM p P N := by
  obtain ⟨-, k, hk1, -⟩ := h1
  obtain ⟨-, j, -, hj2⟩ := h2
  refine ⟨hx, k + j + 1, ?_, ?_⟩
  · have : ((p : LetA O n)) ^ (k + j + 1) • x = ((p : LetA O n)) ^ j • (((p : LetA O n)) ^ k • ((p : LetA O n)) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]; exact P.smul_mem _ hk1
  · have : (letπ : LetA O n) ^ (k + j + 1) • x = (letπ : LetA O n) ^ k • ((letπ : LetA O n) ^ j • (letπ : LetA O n) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]; exact P.smul_mem _ hj2

theorem uniform {p : ℕ} {P N : Submodule (LetA O n) M} (hN : N.FG) (h : N ≤ satM p P N) :
    ∃ c : ℕ, ∀ z ∈ N, ((p : LetA O n)) ^ c • z ∈ P ∧ (letπ : LetA O n) ^ c • z ∈ P := by
  classical
  obtain ⟨G, rfl⟩ := hN
  have hk : ∀ x ∈ G, ∃ k : ℕ, ((p : LetA O n)) ^ k • x ∈ P ∧ (letπ : LetA O n) ^ k • x ∈ P :=
    fun x hx => (h (Submodule.subset_span hx)).2
  choose! k hk using hk
  refine ⟨G.sup k, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem x hx =>
    have hle : k x ≤ G.sup k := Finset.le_sup hx
    obtain ⟨h1, h2⟩ := hk x hx
    constructor
    · rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]; exact P.smul_mem _ h1
    · rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]; exact P.smul_mem _ h2
  | zero => simp
  | add x y _ _ hx hy =>
    exact ⟨by rw [smul_add]; exact P.add_mem hx.1 hy.1, by rw [smul_add]; exact P.add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    exact ⟨by rw [smul_comm]; exact P.smul_mem a hx.1, by rw [smul_comm]; exact P.smul_mem a hx.2⟩

end GlobalTheory.NL.Coker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCharacterOnIdempotentPartOrthogonalityClasse
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial Filter Topology

theorem sum_powerset_neg_one_pow_inter {ι : Type} [DecidableEq ι] (S J : Finset ι) (hJ : J ⊆ S) :
    ∑ I ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card = if J = ∅ then 2 ^ S.card else 0 := by
  have h1 : ∀ I : Finset ι, (-1 : ℝ) ^ (J ∩ I).card = ∏ i ∈ I, (if i ∈ J then (-1 : ℝ) else 1) := by
    intro I
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Finset.filter_mem_eq_inter,
      Finset.inter_comm]
  have h2 : ∑ I ∈ S.powerset, (∏ i ∈ I, (if i ∈ J then (-1 : ℝ) else 1)) =
      ∏ i ∈ S, ((if i ∈ J then (-1 : ℝ) else 1) + 1) := by
    rw [Finset.prod_add]
    simp
  simp_rw [h1]
  rw [h2]
  split_ifs with hJe
  · subst hJe
    simp only [Finset.notMem_empty, if_false, Finset.prod_const]
    norm_num
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hJe
    exact Finset.prod_eq_zero (hJ hj) (by simp [hj])

theorem chi_cl_lift {K : UQ} (B : InvAlg K) {ι : Type} (e : ι → B.A) (I : Finset ι)
    (hmul : ∀ x y : B.A, IsUnit x → IsUnit y → chi B e I (x * y) = chi B e I x * chi B e I y)
    (hnorm : ∀ w : B.A, IsUnit w → chi B e I (w * B.σ w) = 1) :
    ∃ F : B.Cl → ℚ, (∀ k, F k = chi B e I k.rep) ∧
      ∀ x : {x : B.Aˣ // B.σ (x : B.A) = x}, F (Quot.mk _ x) = chi B e I (x.1 : B.A) := by
  refine ⟨Quot.lift (fun x : {x : B.Aˣ // B.σ (x : B.A) = x} => chi B e I (x.1 : B.A)) ?_, ?_, ?_⟩
  · rintro x y ⟨u, hu⟩
    rw [hu, hmul _ _ x.1.isUnit (u.isUnit.mul (u.isUnit.map B.σ)), hnorm _ u.isUnit, mul_one]
  · intro k
    conv_lhs => rw [← Quot.out_eq k]
    rfl
  · intro x; rfl

theorem sum_chi_mul_chi {K : UQ} (B : InvAlg K) {ι : Type} [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι) (hF : IsFrame B e π S) [Fintype B.Cl] (I₀ I : Finset ι) (h₀ : I₀ ⊆ S) (hI : I ⊆ S) :
    ∑ k : B.Cl, chi B e I₀ k.rep * chi B e I k.rep = if I = I₀ then (Fintype.card B.Cl : ℚ) else 0 := by
  obtain ⟨hmul, hnorm, hpi, -⟩ := _root_.GlobalTheory.UnitLemma.Desc.chi_frame_props K B ι e π S hF
  split_ifs with hII
  · subst hII
    have : ∀ k : B.Cl, chi B e I k.rep * chi B e I k.rep = 1 := fun k => eta_sq _
    simp [this]
  · obtain ⟨j, hjS, hj⟩ : ∃ j ∈ S, ¬ (j ∈ I ↔ j ∈ I₀) := by
      by_contra hc
      push_neg at hc
      apply hII
      ext j
      constructor
      · intro h; exact (hc j (hI h)).1 h
      · intro h; exact (hc j (h₀ h)).2 h
    have hp : B.Plus (π j) := (hF.2 j hjS).1
    set v : B.Aˣ := hp.1.unit with hvdef
    have hvv : (v : B.A) = π j := hp.1.unit_spec
    have hv : B.σ (v : B.A) = v := by rw [hvv]; exact hp.2
    have hv' : B.σ ((v⁻¹ : B.Aˣ) : B.A) = ((v⁻¹ : B.Aˣ) : B.A) := by
      calc B.σ ((v⁻¹ : B.Aˣ) : B.A) = ((v⁻¹ : B.Aˣ) : B.A) * ((v : B.A) * B.σ ((v⁻¹ : B.Aˣ) : B.A)) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = ((v⁻¹ : B.Aˣ) : B.A) := by
            rw [← hv, ← map_mul, Units.mul_inv, map_one, mul_one]
    have hsign : chi B e I₀ (π j) * chi B e I (π j) = -1 := by
      have a0 := hpi I₀ {j} h₀ (Finset.singleton_subset_iff.2 hjS)
      have a1 := hpi I {j} hI (Finset.singleton_subset_iff.2 hjS)
      rw [Finset.prod_singleton] at a0 a1
      rw [a0, a1]
      by_cases hjI : j ∈ I
      · have hjI0 : j ∉ I₀ := fun h => hj ⟨fun _ => h, fun _ => hjI⟩
        simp [Finset.singleton_inter_of_mem hjI, Finset.singleton_inter_of_notMem hjI0]
      · have hjI0 : j ∈ I₀ := by by_contra h; exact hj ⟨fun h' => absurd h' hjI, fun h' => absurd h' h⟩
        simp [Finset.singleton_inter_of_mem hjI0, Finset.singleton_inter_of_notMem hjI]
    obtain ⟨F₀, hF₀, hF₀mk⟩ := chi_cl_lift B e I₀ (hmul I₀) (hnorm I₀)
    obtain ⟨F₁, hF₁, hF₁mk⟩ := chi_cl_lift B e I (hmul I) (hnorm I)
    let T : B.Cl → B.Cl := Quot.map
      (fun x : {x : B.Aˣ // B.σ (x : B.A) = x} =>
        (⟨v * x.1, by rw [Units.val_mul, map_mul, hv, x.2]⟩ : {x : B.Aˣ // B.σ (x : B.A) = x}))
      (by rintro x y ⟨u, hu⟩; exact ⟨u, by simp only [Units.val_mul]; rw [hu, mul_assoc]⟩)
    let T' : B.Cl → B.Cl := Quot.map
      (fun x : {x : B.Aˣ // B.σ (x : B.A) = x} =>
        (⟨v⁻¹ * x.1, by rw [Units.val_mul, map_mul, hv', x.2]⟩ : {x : B.Aˣ // B.σ (x : B.A) = x}))
      (by rintro x y ⟨u, hu⟩; exact ⟨u, by simp only [Units.val_mul]; rw [hu, mul_assoc]⟩)
    let E : B.Cl ≃ B.Cl :=
      { toFun := T, invFun := T'
        left_inv := fun k => Quot.inductionOn k fun x => congrArg (Quot.mk _) (Subtype.ext (inv_mul_cancel_left v x.1))
        right_inv := fun k => Quot.inductionOn k fun x => congrArg (Quot.mk _) (Subtype.ext (mul_inv_cancel_left v x.1)) }
    have key : ∀ k, F₀ (E k) * F₁ (E k) = -(F₀ k * F₁ k) := by
      intro k
      induction k using Quot.ind with
      | mk x =>
        change F₀ (Quot.mk _ _) * F₁ (Quot.mk _ _) = _
        rw [hF₀mk, hF₀mk, hF₁mk, hF₁mk, Units.val_mul, hmul I₀ _ _ v.isUnit x.1.isUnit,
          hmul I _ _ v.isUnit x.1.isUnit, hvv]
        linear_combination (chi B e I₀ (x.1 : B.A) * chi B e I (x.1 : B.A)) * hsign
    have hs : ∑ k : B.Cl, F₀ k * F₁ k = 0 := by
      have := Equiv.sum_comp E (fun k => F₀ k * F₁ k)
      simp only [key, Finset.sum_neg_distrib] at this
      linarith
    simpa [hF₀, hF₁] using hs

theorem sum_chi_ell_cl : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι), IsFrame B e π S → Finite B.Cl → ∀ (ℓ : B.A → ℝ) (h : Finset ι → ℝ),
    (∀ I ⊆ S, ∀ x, B.Plus x → ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) =
      (chi B e I x : ℝ) * h I) →
    ∀ I ⊆ S, ∑ᶠ k : B.Cl, (chi B e I k.rep : ℝ) * ℓ k.rep = (Nat.card B.Cl : ℝ) / 2 ^ S.card * h I := by
  intro K B ι _ _ e π S hF hfin ℓ h hyp I₀ h₀
  haveI := Fintype.ofFinite B.Cl
  have inv : ∀ x, B.Plus x → (2 : ℝ) ^ S.card * ℓ x = ∑ I ∈ S.powerset, (chi B e I x : ℝ) * h I := by
    intro x hx
    calc (2 : ℝ) ^ S.card * ℓ x
        = ∑ J ∈ S.powerset, (∑ I ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card) * ℓ ((∏ j ∈ J, π j) * x) := by
          rw [Finset.sum_eq_single ∅]
          · simp [sum_powerset_neg_one_pow_inter S ∅ (Finset.empty_subset _)]
          · intro J hJ hJe
            rw [sum_powerset_neg_one_pow_inter S J (Finset.mem_powerset.1 hJ), if_neg hJe, zero_mul]
          · intro hn; exact absurd (Finset.empty_mem_powerset S) hn
      _ = ∑ I ∈ S.powerset, ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) := by
          simp_rw [Finset.sum_mul]; exact Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun I hI => hyp I (Finset.mem_powerset.1 hI) x hx
  have hplus : ∀ k : B.Cl, B.Plus k.rep := fun k => ⟨(Quot.out k).1.isUnit, (Quot.out k).2⟩
  have e1 : ∀ k : B.Cl, ℓ k.rep = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, (chi B e I k.rep : ℝ) * h I := by
    intro k; rw [← inv _ (hplus k), ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have orth : ∀ I ∈ S.powerset, ∑ k : B.Cl, (chi B e I₀ k.rep : ℝ) * (chi B e I k.rep : ℝ) =
      if I = I₀ then (Fintype.card B.Cl : ℝ) else 0 := by
    intro I hI
    have := sum_chi_mul_chi B e π S hF I₀ I h₀ (Finset.mem_powerset.1 hI)
    split_ifs at this ⊢ <;> exact_mod_cast this
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  simp_rw [e1]
  calc ∑ k : B.Cl, (chi B e I₀ k.rep : ℝ) * (((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, (chi B e I k.rep : ℝ) * h I)
      = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, h I * ∑ k : B.Cl, (chi B e I₀ k.rep : ℝ) * (chi B e I k.rep : ℝ) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun k _ => by ring
    _ = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, h I * (if I = I₀ then (Fintype.card B.Cl : ℝ) else 0) := by
        rw [Finset.sum_congr rfl fun I hI => by rw [orth I hI]]
    _ = (Fintype.card B.Cl : ℝ) / 2 ^ S.card * h I₀ := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_powerset.2 h₀, if_true]
        ring

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrthonormalIffUnitary
section
open GlobalTheory.UnitLemma Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.UnitLemma.BaseChange

variable {K : UQ} (B : InvAlg K)

theorem herm_sum_left {ι : Type} (s : Finset ι) (x : B.A) (f : ι → B.A) (z : B.A) :
    B.herm x (∑ k ∈ s, f k) z = ∑ k ∈ s, B.herm x (f k) z := by
  unfold InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, Finset.sum_mul, map_sum]

theorem herm_sum_right {ι : Type} (s : Finset ι) (x y : B.A) (f : ι → B.A) :
    B.herm x y (∑ k ∈ s, f k) = ∑ k ∈ s, B.herm x y (f k) := by
  unfold InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, map_sum]

theorem herm_basis_change (x : B.A) {n : ℕ} (e e' : Module.Basis (Fin n) K.E B.A)
    (he : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) (i j : Fin n) :
    B.herm x (e' i) (e' j) = ∑ k, e.toMatrix e' k i * K.c (e.toMatrix e' k j) := by
  have hi := e.sum_toMatrix_smul_self e' i
  have hj := e.sum_toMatrix_smul_self e' j
  rw [← hi, ← hj, herm_sum_left]
  simp_rw [herm_sum_right, GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, he]
  simp [mul_ite, Finset.sum_ite_eq]

theorem orthonormal_iff_unitary : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (n : ℕ) (e e' : Module.Basis (Fin n) K.E B.A),
    (∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) →
    ((∀ i j, B.herm x (e' i) (e' j) = if i = j then 1 else 0) ↔ ((e.toMatrix e').map K.c)ᵀ * e.toMatrix e' = 1) := by
  intro K B x n e e' he
  have key := herm_basis_change B x e e' he
  have hm : ∀ i j, (((e.toMatrix e').map K.c)ᵀ * e.toMatrix e') j i = B.herm x (e' i) (e' j) := by
    intro i j
    rw [key, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by simp [mul_comm]
  constructor
  · intro h'
    ext j i
    rw [hm, h', Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · intro hu i j
    rw [← hm, hu, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]

end GlobalTheory.UnitLemma.BaseChange
end
end

