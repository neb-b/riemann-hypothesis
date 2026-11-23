module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CubeCutRegularSequence
section
open CategoryTheory GlobalTheory

namespace GlobalTheory

namespace CubeCut

variable {K : Type} [CommRing K] {I : Type} [LinearOrder I]

def ExactMod (A : Cube.{0} I K) (J : ∀ s, Submodule K (A.obj s)) : Prop :=
  (∀ x : Cube.Term A 0, (∀ s, Cube.d A 0 x s ∈ J s.1) → ∀ s, x s ∈ J s.1) ∧
    ∀ (p : ℕ) (x : Cube.Term A (p + 1)), (∀ s, Cube.d A (p + 1) x s ∈ J s.1) →
      ∃ y : Cube.Term A p, ∀ s, (x - Cube.d A p y) s ∈ J s.1

theorem d_mem {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (hJ : ∀ {s t : Finset I} (h : s ⊆ t) (x : A.obj s), x ∈ J s → Cube.res A h x ∈ J t)
    {p : ℕ} {x : Cube.Term A p} (hx : ∀ s, x s ∈ J s.1) (t) : Cube.d A p x t ∈ J t.1 := by
  rw [Cube.d_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h1 : Cube.res A (Finset.erase_subset i.1 t.1) (x (Cube.eraseIdx t i)) ∈ J t.1 :=
    hJ (Finset.erase_subset i.1 t.1) _ (hx (Cube.eraseIdx t i))
  exact Submodule.smul_of_tower_mem _ _ h1

theorem exactMod_of_exact {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (hJ : ∀ s, J s = ⊥) (h : ∀ p, (cubeComplex A).ExactAt p) : ExactMod A J := by
  refine ⟨fun x hx s => ?_, fun p x hx => ?_⟩
  · have h0 : Cube.d A 0 x = 0 := funext fun s => by simpa [hJ] using hx s
    have h1 := (cubeComplex_exactAt_zero_iff' A).1 (h 0) (h0.trans (map_zero _).symm)
    simp [h1, hJ]
  · have h0 : Cube.d A (p + 1) x = 0 := funext fun s => by simpa [hJ] using hx s
    obtain ⟨y, hy⟩ := ((cubeComplex_exactAt_succ_iff A p).1 (h (p + 1)) x).1 h0
    exact ⟨y, fun s => by simp [hy, hJ]⟩

theorem ExactMod.mem_empty {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (h : ExactMod A J) (y : A.obj ∅)
    (hy : ∀ a : I, Cube.res A (Finset.empty_subset {a}) y ∈ J {a}) : y ∈ J ∅ := by
  have h1 := h.1 ((Cube.termZeroEquiv A).symm y) (fun s => by
    rw [Cube.d_zero_apply, LinearEquiv.apply_symm_apply, Cube.aug_apply]
    obtain ⟨s, hs⟩ := s
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs
    exact hy a) ⟨∅, rfl⟩
  have heval : (Cube.termZeroEquiv A).symm y ⟨∅, rfl⟩ = y := by
    simp [Cube.termZeroEquiv]
  rw [heval] at h1
  exact h1

theorem ExactMod.exists_glue {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (h : ExactMod A J) (y : ∀ a : I, A.obj {a})
    (hy : ∀ a a' : I, Cube.res A (show ({a} : Finset I) ⊆ {a, a'} by simp) (y a) -
      Cube.res A (show ({a'} : Finset I) ⊆ {a, a'} by simp) (y a') ∈ J {a, a'}) :
    ∃ y₀ : A.obj ∅, ∀ a, Cube.res A (Finset.empty_subset {a}) y₀ - y a ∈ J {a} := by
  have key : ∀ i j : I, (hij : i < j) →
      Cube.d A 1 (Cube.termOneEquiv A y) ⟨{i, j}, Finset.card_pair hij.ne⟩ ∈ J {i, j} := by
    intro i j hij
    rw [Cube.d_one_apply_pair A _ hij]
    simp only [Cube.termOneEquiv_apply]
    have h1 := (J {i, j}).neg_mem (hy i j)
    rwa [neg_sub] at h1
  have hx : ∀ s, Cube.d A 1 (Cube.termOneEquiv A y) s ∈ J s.1 := by
    rintro ⟨t, ht⟩
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 ht
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact key i j h'
    · revert ht
      rw [Finset.pair_comm i j]
      intro ht
      exact key j i h'
  obtain ⟨z, hz⟩ := h.2 0 (Cube.termOneEquiv A y) hx
  refine ⟨Cube.termZeroEquiv A z, fun a => ?_⟩
  have h1 := hz ⟨{a}, Finset.card_singleton a⟩
  rw [Pi.sub_apply, Cube.d_zero_apply, Cube.aug_apply, Cube.termOneEquiv_apply] at h1
  have h2 := (J {a}).neg_mem h1
  rwa [neg_sub] at h2

private theorem exists_term_d_sub_termMap_mem {A B : Cube.{0} I K} {JA : ∀ s, Submodule K (A.obj s)}
    {JB J : ∀ s, Submodule K (B.obj s)} (φ : A ⟶ B) (hA : ExactMod A JA)
    (hJB : ∀ {s t : Finset I} (h : s ⊆ t) (x : B.obj s), x ∈ JB s → Cube.res B h x ∈ JB t)
    (hφ : ∀ s x, x ∈ JA s → (φ.app s).hom x ∈ JB s)
    (hinj : ∀ s, s.Nonempty → ∀ x, (φ.app s).hom x ∈ JB s → x ∈ JA s)
    (hJ : ∀ s, J s = JB s ⊔ LinearMap.range (φ.app s).hom) {k : ℕ} (x : Cube.Term B k)
    (hx : ∀ s, Cube.d B k x s ∈ J s.1) :
    ∃ a₁ : Cube.Term A k, ∀ s, Cube.d B k (x - Cube.termMap φ k a₁) s ∈ JB s.1 := by
  have hx' : ∀ t : {s : Finset I // s.card = k + 1},
      ∃ a : A.obj t.1, Cube.d B k x t - (φ.app t.1).hom a ∈ JB t.1 := by
    intro t
    have h1 := hx t
    rw [hJ, Submodule.mem_sup] at h1
    obtain ⟨u, hu, _, ⟨a, rfl⟩, hua⟩ := h1
    refine ⟨a, ?_⟩
    rw [← hua, add_sub_cancel_right]
    exact hu
  choose a ha using hx'
  have hb : ∀ t, (Cube.d B k x - Cube.termMap φ (k + 1) a) t ∈ JB t.1 := fun t => by
    simpa using ha t
  have hda : ∀ u, Cube.d A (k + 1) a u ∈ JA u.1 := by
    intro u
    apply hinj u.1 (Finset.card_pos.1 (by rw [u.2]; omega))
    have h1 := congrFun (Cube.termMap_d φ (k + 1) a) u
    simp only [Cube.termMap_apply] at h1
    have h2 : (φ.app u.1).hom (Cube.d A (k + 1) a u) =
        -Cube.d B (k + 1) (Cube.d B k x - Cube.termMap φ (k + 1) a) u := by
      rw [h1, map_sub, Cube.d_d]
      simp
    rw [h2]
    exact neg_mem (d_mem hJB hb u)
  obtain ⟨a₁, ha₁⟩ := hA.2 k a hda
  refine ⟨a₁, fun s => ?_⟩
  have h1 : Cube.d B k (x - Cube.termMap φ k a₁) s =
      (Cube.d B k x - Cube.termMap φ (k + 1) a) s + (φ.app s.1).hom ((a - Cube.d A k a₁) s) := by
    rw [map_sub, ← Cube.termMap_d]
    simp only [Pi.sub_apply, Cube.termMap_apply, map_sub]
    abel
  rw [h1]
  exact add_mem (hb s) (hφ _ _ (ha₁ s))

theorem ExactMod.cut {A B : Cube.{0} I K} {JA : ∀ s, Submodule K (A.obj s)}
    {JB J : ∀ s, Submodule K (B.obj s)} (φ : A ⟶ B) (hA : ExactMod A JA) (hB : ExactMod B JB)
    (hJB : ∀ {s t : Finset I} (h : s ⊆ t) (x : B.obj s), x ∈ JB s → Cube.res B h x ∈ JB t)
    (hφ : ∀ s x, x ∈ JA s → (φ.app s).hom x ∈ JB s)
    (hinj : ∀ s, s.Nonempty → ∀ x, (φ.app s).hom x ∈ JB s → x ∈ JA s)
    (hJ : ∀ s, J s = JB s ⊔ LinearMap.range (φ.app s).hom) : ExactMod B J := by
  refine ⟨fun x hx s => ?_, fun p x hx => ?_⟩
  · obtain ⟨a₁, ha₁⟩ := exists_term_d_sub_termMap_mem φ hA hJB hφ hinj hJ x hx
    have h1 := hB.1 _ ha₁ s
    have h2 : x s = (x - Cube.termMap φ 0 a₁) s + (φ.app s.1).hom (a₁ s) := by simp
    rw [h2, hJ]
    exact Submodule.add_mem_sup h1 (LinearMap.mem_range_self _ _)
  · obtain ⟨a₁, ha₁⟩ := exists_term_d_sub_termMap_mem φ hA hJB hφ hinj hJ x hx
    obtain ⟨y, hy⟩ := hB.2 p _ ha₁
    refine ⟨y, fun s => ?_⟩
    have h2 : (x - Cube.d B p y) s =
        (x - Cube.termMap φ (p + 1) a₁ - Cube.d B p y) s + (φ.app s.1).hom (a₁ s) := by
      simp only [Pi.sub_apply, Cube.termMap_apply]
      abel
    rw [h2, hJ]
    exact Submodule.add_mem_sup (hy s) (LinearMap.mem_range_self _ _)

section Family

variable {g : ℕ} {A B : Cube.{0} I K} (φ : Fin g → (A ⟶ B))

abbrev imSum (k : ℕ) (s : Finset I) : Submodule K (B.obj s) :=
  ⨆ (j : Fin g) (_ : (j : ℕ) < k), LinearMap.range ((φ j).app s).hom


omit [LinearOrder I] in
theorem res_mem_imSum (k : ℕ) {s t : Finset I} (h : s ⊆ t) (x : B.obj s)
    (hx : x ∈ imSum φ k s) : Cube.res B h x ∈ imSum φ k t := by
  have key : imSum φ k s ≤ (imSum φ k t).comap (Cube.res B h) := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨a, rfl⟩
    rw [Submodule.mem_comap, ← Cube.app_res]
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (LinearMap.mem_range_self _ _))
  exact key hx


omit [LinearOrder I] in
theorem imSum_succ (i : Fin g) (s : Finset I) :
    imSum φ (i + 1) s = imSum φ i s ⊔ LinearMap.range ((φ i).app s).hom := by
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    by_cases h : (j : ℕ) < i
    · exact le_sup_of_le_left (le_iSup_of_le j (le_iSup_of_le h le_rfl))
    · have hji : j = i := Fin.ext (by omega)
      subst hji
      exact le_sup_right
  · exact sup_le (iSup₂_le fun j hj => le_iSup_of_le j (le_iSup_of_le (by omega) le_rfl))
      (le_iSup_of_le i (le_iSup_of_le (by omega) le_rfl))

end Family

end CubeCut


open CubeCut in
theorem cube_cut_regular_sequence : ∀ (K : Type) [CommRing K] (I : Type) [LinearOrder I] [Fintype I] (g : ℕ) (n : ℤ) (C : ℤ → Cube.{0} I K) (mu : Fin g → ∀ l l', C l ⟶ C l'), 0 < n → (∀ i j l l' l'', l' = l + n → l'' = l' + n → mu i l l' ≫ mu j l' l'' = mu j l l' ≫ mu i l' l'') → (∀ (T : Finset I), T.Nonempty → ∀ (i : Fin g) (l l' : ℤ) (y : (C l).obj T), l' = l + n → ((mu i l l').app T).hom y ∈ (⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j l l').app T).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j (l - n) l).app T).hom) → (∀ l, 0 < l → ∀ p, (cubeComplex (C l)).ExactAt p) → (∀ (i : Fin g) (l l' : ℤ) (y : (C l).obj ∅), l' = l + n → (i : ℕ) * n < l → ((mu i l l').app ∅).hom y ∈ (⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j l l').app ∅).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j (l - n) l).app ∅).hom) ∧ ∀ l : ℤ, g * n < l → (∀ y : (C l).obj ∅, (∀ a : I, Cube.res (C l) (Finset.empty_subset {a}) y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a}).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app ∅).hom) ∧ ∀ y : ∀ a : I, (C l).obj {a}, (∀ a a' : I, Cube.res (C l) (show ({a} : Finset I) ⊆ {a, a'} by simp) (y a) - Cube.res (C l) (show ({a'} : Finset I) ⊆ {a, a'} by simp) (y a') ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a, a'}).hom) → ∃ y₀ : (C l).obj ∅, ∀ a, Cube.res (C l) (Finset.empty_subset {a}) y₀ - y a ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a}).hom := by
  intro K _ I _ _ g n C mu hn hcomm hreg hac
  have P : ∀ k : ℕ, k ≤ g → ∀ l₀ l : ℤ, l = l₀ + n → (k : ℤ) * n < l →
      CubeCut.ExactMod (C l) (fun s => CubeCut.imSum (fun j => mu j l₀ l) k s) := by
    intro k
    induction k with
    | zero =>
      intro _ l₀ l _ hlt
      refine CubeCut.exactMod_of_exact (fun s => ?_) (hac l (by simpa using hlt))
      simp [CubeCut.imSum]
    | succ k ih =>
      intro hk l₀ l hl hlt
      push_cast at hlt
      have hA := ih (by omega) (l₀ - n) l₀ (by ring) (by linarith)
      have hB := ih (by omega) l₀ l hl (by linarith)
      let i : Fin g := ⟨k, by omega⟩
      refine CubeCut.ExactMod.cut (mu i l₀ l) hA hB
        (fun h x hx => CubeCut.res_mem_imSum _ _ h x hx) ?_
        (fun s hs x hx => hreg s hs i l₀ l x hl hx)
        (fun s => CubeCut.imSum_succ (fun j => mu j l₀ l) i s)
      intro s x hx
      have key : CubeCut.imSum (fun j => mu j (l₀ - n) l₀) k s ≤
          (CubeCut.imSum (fun j => mu j l₀ l) k s).comap ((mu i l₀ l).app s).hom := by
        refine iSup₂_le fun j hj => ?_
        rintro _ ⟨z, rfl⟩
        rw [Submodule.mem_comap]
        have e := congrArg (fun f => (f.app s).hom z) (hcomm j i (l₀ - n) l₀ l (by ring) hl)
        simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at e
        rw [e]
        exact Submodule.mem_iSup_of_mem j
          (Submodule.mem_iSup_of_mem hj (LinearMap.mem_range_self _ _))
      exact key hx
  refine ⟨fun i l l' y hl' hlt hy => ?_, fun l hlt => ?_⟩
  · have hE := P i i.2.le (l - n) l (by ring) hlt
    refine hE.mem_empty y fun a => ?_
    refine hreg {a} (Finset.singleton_nonempty a) i l l' _ hl' ?_
    rw [Cube.app_res]
    exact CubeCut.res_mem_imSum _ _ _ _ hy
  · have hE := P g le_rfl (l - n) l (by ring) hlt
    exact ⟨hE.mem_empty, hE.exists_glue⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsCompleteDiscreteValuationRingWithResidues
section
open IsLocalRing Polynomial

namespace GlobalTheory

namespace ResidueExtension

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]

theorem injective_of_map_ne_zero {B : Type} [CommRing B] [IsDomain B] (j : O →+* B) {π : O}
    (hπ : Irreducible π) (h : j π ≠ 0) : Function.Injective j := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
  rw [map_mul, map_pow] at hx
  exact mul_ne_zero (u.isUnit.map j).ne_zero (pow_ne_zero n h) hx

theorem exists_localization {A : Type} [CommRing A] [IsNoetherianRing A] (i : O →+* A)
    (ψ : A →+* Ω) {π : O} (hπ : Irreducible π) (hker : RingHom.ker ψ = Ideal.span {i π})
    (hreg : ∀ x, i π * x = 0 → x = 0) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (j : O →+* B) (r' : B →+* Ω), Function.Injective j ∧ r'.comp j = ψ.comp i ∧
      RingHom.ker r' = maximalIdeal B ∧ Set.range ψ ⊆ Set.range r' := by
  have hp : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let B := Localization.AtPrime (RingHom.ker ψ)
  have hu : ∀ y : (RingHom.ker ψ).primeCompl, IsUnit (ψ y) := fun y =>
    isUnit_iff_ne_zero.mpr y.2
  let r' : B →+* Ω := IsLocalization.lift hu
  have hr' : ∀ x, r' (algebraMap A B x) = ψ x := fun x => IsLocalization.lift_eq hu x
  have hmax : maximalIdeal B = Ideal.span {algebraMap A B (i π)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    conv_lhs => enter [2]; rw [hker]
    rw [Ideal.map_span, Set.image_singleton]
  have hpow : ∀ (n : ℕ) x, i π ^ n * x = 0 → x = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x hx
      rw [pow_succ, mul_assoc] at hx
      exact hreg x (ih _ hx)
  have hn : ¬ IsNilpotent (algebraMap A B (i π)) := by
    rintro ⟨n, hn⟩
    rw [← map_pow, IsLocalization.map_eq_zero_iff (RingHom.ker ψ).primeCompl] at hn
    obtain ⟨m, hm⟩ := hn
    have := hpow n m (by rw [mul_comm]; exact hm)
    exact m.2 (this ▸ zero_mem _)
  obtain ⟨hd, hdvr, hirr⟩ := isDiscreteValuationRing_of_maximalIdeal_eq_span hmax hn
  refine ⟨B, inferInstance, hd, hdvr, (algebraMap A B).comp i, r',
    injective_of_map_ne_zero _ hπ hirr.ne_zero, RingHom.ext fun x => hr' _, ?_, ?_⟩
  · refine ((maximalIdeal.isMaximal B).eq_of_le (RingHom.ker_ne_top r') ?_).symm
    rw [hmax, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, hr', ← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self _
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, hr' x⟩

theorem exists_generator (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) (a : Ω) {π : O}
    (hπ : Irreducible π) :
    ∃ G : O[X], (G.Monic ∨ G = 0) ∧ G.eval₂ r a = 0 ∧
      ∀ f : O[X], f.eval₂ r a = 0 → ∃ g h, f = G * g + C π * h := by
  let rb : ResidueField O →+* Ω :=
    Ideal.Quotient.lift (maximalIdeal O) r fun x hx => by rwa [← hr] at hx
  let _ : Algebra (ResidueField O) Ω := rb.toAlgebra
  have hev : ∀ f : O[X], aeval a (f.map (residue O)) = f.eval₂ r a := by
    intro f
    rw [aeval_def, eval₂_map]
    rfl
  obtain ⟨G, hG, hG'⟩ : ∃ G : O[X], (G.Monic ∨ G = 0) ∧
      G.map (residue O) = minpoly (ResidueField O) a := by
    by_cases h : IsIntegral (ResidueField O) a
    · obtain ⟨G, h1, -, h2⟩ := lifts_and_degree_eq_and_monic
        ((mem_lifts _).mpr (map_surjective (residue O) residue_surjective _)) (minpoly.monic h)
      exact ⟨G, Or.inl h2, h1⟩
    · exact ⟨0, Or.inr rfl, by rw [minpoly.eq_zero h, Polynomial.map_zero]⟩
  refine ⟨G, hG, by rw [← hev, hG', minpoly.aeval], fun f hf => ?_⟩
  rw [← hev] at hf
  obtain ⟨g', hg'⟩ := minpoly.dvd _ _ hf
  obtain ⟨g, rfl⟩ := map_surjective (residue O) residue_surjective g'
  have h1 : f - G * g ∈ RingHom.ker (mapRingHom (residue O)) := by
    rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, hG', hg', sub_self]
  rw [ker_mapRingHom, ker_residue, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at h1
  obtain ⟨h, hh⟩ := h1
  exact ⟨g, h, by rw [← hh]; ring⟩

theorem exists_step (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) (a : Ω) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (j : O →+* B) (r' : B →+* Ω), Function.Injective j ∧ r'.comp j = r ∧
      RingHom.ker r' = maximalIdeal B ∧ a ∈ Set.range r' := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨G, hG, h0, hgen⟩ := exists_generator r hr a hπ
  have hrπ : r π = 0 := by
    rw [← RingHom.mem_ker, hr, hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self _
  have hk : RingHom.ker (AdjoinRoot.lift r a h0) = Ideal.span {AdjoinRoot.of G π} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
      rw [RingHom.mem_ker, AdjoinRoot.lift_mk] at hx
      obtain ⟨g, h, rfl⟩ := hgen f hx
      rw [map_add (f := _), map_mul, AdjoinRoot.mk_self, zero_mul, zero_add, map_mul, AdjoinRoot.mk_C]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, AdjoinRoot.lift_of, hrπ]
  have hreg : ∀ x, AdjoinRoot.of G π * x = 0 → x = 0 := by
    intro x hx
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [← AdjoinRoot.mk_C, ← map_mul, AdjoinRoot.mk_eq_zero] at hx
    rw [AdjoinRoot.mk_eq_zero]
    rcases hG with hG | rfl
    · rw [← modByMonic_eq_zero_iff_dvd hG] at hx ⊢
      rw [← smul_eq_C_mul, smul_modByMonic] at hx
      exact (smul_eq_zero.mp hx).resolve_left hπ.ne_zero
    · rw [zero_dvd_iff] at hx ⊢
      exact (mul_eq_zero.mp hx).resolve_left (C_ne_zero.mpr hπ.ne_zero)
  obtain ⟨B, _, _, _, j, r', h1, h2, h3, h4⟩ := exists_localization (AdjoinRoot.of G)
    (AdjoinRoot.lift r a h0) hπ hk hreg
  exact ⟨B, _, ‹_›, ‹_›, j, r', h1, h2.trans (AdjoinRoot.lift_comp_of h0), h3,
    h4 ⟨_, AdjoinRoot.lift_root h0⟩⟩

theorem exists_finset (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) (S : Finset Ω) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (j : O →+* B) (r' : B →+* Ω), Function.Injective j ∧ r'.comp j = r ∧
      RingHom.ker r' = maximalIdeal B ∧ ∀ a ∈ S, a ∈ Set.range r' := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨O, _, ‹_›, ‹_›, RingHom.id O, r, Function.injective_id, rfl, hr, by simp⟩
  | insert a S _ ih =>
    obtain ⟨B, _, _, _, j, r', h1, h2, h3, h4⟩ := ih
    obtain ⟨B', _, _, _, j', r'', h1', h2', h3', h4'⟩ := exists_step r' h3 a
    refine ⟨B', _, ‹_›, ‹_›, j'.comp j, r'', h1'.comp h1,
      by rw [← RingHom.comp_assoc, h2', h2], h3', fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact h4'
    · obtain ⟨y, rfl⟩ := h4 b hb
      exact ⟨j' y, RingHom.congr_fun h2' y⟩

theorem exists_completion (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) :
    ∃ r' : AdicCompletion (maximalIdeal O) O →+* Ω,
      r'.comp (algebraMap O _) = r ∧ RingHom.ker r' = maximalIdeal _ := by
  let rb : ResidueField O →+* Ω :=
    Ideal.Quotient.lift (maximalIdeal O) r fun x hx => by rwa [← hr] at hx
  let e := RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective O)
  refine ⟨(rb.comp e.symm.toRingHom).comp (residue _), RingHom.ext fun x => ?_, ?_⟩
  · have : e.symm (residue _ (algebraMap O _ x)) = residue O x := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    change rb (e.symm (residue _ (algebraMap O _ x))) = r x
    rw [this]
    rfl
  · rw [RingHom.ker_comp_of_injective _ (RingHom.injective _), ker_residue]

end ResidueExtension

theorem exists_complete_discreteValuationRing_with_residues :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
      (r : O →+* Ω) (S : Finset Ω), RingHom.ker r = IsLocalRing.maximalIdeal O →
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
        (j : O →+* O') (r' : O' →+* Ω), IsAdicComplete (IsLocalRing.maximalIdeal O') O' ∧
        Function.Injective j ∧ IsLocalHom j ∧ r'.comp j = r ∧
        RingHom.ker r' = IsLocalRing.maximalIdeal O' ∧ ∀ a ∈ S, a ∈ Set.range r' := by
  intro O _ _ _ Ω _ r S hr
  obtain ⟨B, _, _, _, j, r', h1, h2, h3, h4⟩ := ResidueExtension.exists_finset r hr S
  obtain ⟨r'', h5, h6⟩ := ResidueExtension.exists_completion r' h3
  have h7 : r''.comp ((algebraMap B (AdicCompletion (maximalIdeal B) B)).comp j) = r := by
    rw [← RingHom.comp_assoc, h5, h2]
  refine ⟨AdicCompletion (maximalIdeal B) B, inferInstance, inferInstance, inferInstance,
    (algebraMap B _).comp j, r'', inferInstance,
    (algebraMap_adicCompletion_injective_of_dvr B).comp h1, ⟨fun x hx => ?_⟩, h7, h6,
    fun a ha => ?_⟩
  · rw [← notMem_maximalIdeal, ← hr, RingHom.mem_ker, ← h7]
    exact (hx.map r'').ne_zero
  · obtain ⟨y, rfl⟩ := h4 a ha
    exact ⟨_, RingHom.congr_fun h5 y⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPowSpanXLeOfDense
section
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem exists_pow_span_X_le_of_dense (K : Type) [Field K] (g N : ℕ)
    (I : Ideal (MvPowerSeries (Fin g) K)) (ρ : Fin N → MvPowerSeries (Fin g) K)
    (h : ∀ (r : ℕ) (G : MvPowerSeries (Fin g) K), ∃ v : Fin N → K,
      G - ∑ k, v k • ρ k ∈ I ⊔ Ideal.span (Set.range MvPowerSeries.X) ^ r) :
    ∃ r : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) K)) ^ r ≤ I := by
  set J : Ideal (MvPowerSeries (Fin g) K) := Ideal.span (Set.range MvPowerSeries.X) with hJ
  let L : (Fin N → K) →ₗ[K] MvPowerSeries (Fin g) K := Fintype.linearCombination K ρ
  have hL : ∀ v, L v = ∑ k, v k • ρ k := fun v => Fintype.linearCombination_apply K ρ v
  let V : ℕ →o (Submodule K (Fin N → K))ᵒᵈ :=
    ⟨fun r => OrderDual.toDual (((I ⊔ J ^ r).restrictScalars K).comap L), by
      intro a b hab
      change ((I ⊔ J ^ b).restrictScalars K).comap L ≤ ((I ⊔ J ^ a).restrictScalars K).comap L
      intro v hv
      exact (sup_le_sup_left (Ideal.pow_le_pow_right hab) I) hv⟩
  obtain ⟨r, hr⟩ := IsArtinian.monotone_stabilizes V
  have hV : ∀ v, L v ∈ I ⊔ J ^ r → L v ∈ I ⊔ J ^ (r + 1) := by
    intro v hv
    have e : ((I ⊔ J ^ r).restrictScalars K).comap L = ((I ⊔ J ^ (r + 1)).restrictScalars K).comap L :=
      hr (r + 1) (Nat.le_succ r)
    have : v ∈ ((I ⊔ J ^ r).restrictScalars K).comap L := hv
    rw [e] at this
    exact this
  have hfg : J.FG := Submodule.fg_span (Set.finite_range _)
  have hjac : J ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  refine ⟨r, Submodule.le_of_le_smul_of_le_jacobson_bot (N' := J ^ r) (N := I) (I := J)
    (Ideal.FG.pow hfg) hjac ?_⟩
  intro G hG
  obtain ⟨v, hv⟩ := h (r + 1) G
  rw [← hL] at hv
  have h1 : L v ∈ I ⊔ J ^ r := by
    have h2 : G - L v ∈ I ⊔ J ^ r :=
      (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ r)) I) hv
    have h3 : G ∈ I ⊔ J ^ r := Ideal.mem_sup_right hG
    simpa using Ideal.sub_mem _ h3 h2
  have h4 := Ideal.add_mem _ hv (hV v h1)
  rw [sub_add_cancel, pow_succ'] at h4
  exact h4

theorem exists_sub_mem_of_dense : ∀ (K : Type) [Field K] (g N : ℕ) (Y : Type) [Finite Y] (I : Y → Ideal (MvPowerSeries (Fin g) K)) (ρ : Y → Fin N → MvPowerSeries (Fin g) K), (∀ (r : ℕ) (G : Y → MvPowerSeries (Fin g) K), ∃ v : Fin N → K, ∀ y, G y - ∑ k, v k • ρ y k ∈ I y ⊔ Ideal.span (Set.range MvPowerSeries.X) ^ r) → ∀ G : Y → MvPowerSeries (Fin g) K, ∃ v : Fin N → K, ∀ y, G y - ∑ k, v k • ρ y k ∈ I y := by
  intro K _ g N Y _ I ρ h G
  have hy : ∀ y, ∃ r : ℕ,
      Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) K)) ^ r ≤ I y :=
    fun y => exists_pow_span_X_le_of_dense K g N (I y) (ρ y) fun r F => by
      obtain ⟨v, hv⟩ := h r (fun _ => F)
      exact ⟨v, hv y⟩
  choose r hr using hy
  obtain ⟨R, hR⟩ := (Set.finite_range r).bddAbove
  obtain ⟨v, hv⟩ := h R G
  refine ⟨v, fun y => ?_⟩
  exact (sup_le le_rfl ((Ideal.pow_le_pow_right (hR ⟨y, rfl⟩)).trans (hr y))) (hv y)

end GlobalTheory.KeyKa
end

