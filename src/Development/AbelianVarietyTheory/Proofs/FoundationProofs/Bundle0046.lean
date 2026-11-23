module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0057
public import GroundTheory.PAdicHodge.AxLemma
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsGluedTowerLevels
section
noncomputable section

namespace GlobalTheory.LevGlue

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem der_pow_val {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (hD : GlobalTheory.KumDlog.IsDer S D)
    (hS : ∀ x ∈ S, IsInt (p := p) x) (hp : (p : Ω) ≠ 0) {x c : Ω} {m j : ℕ} (hx : x ∈ S)
    (h : IsInt (p := p) (D x - c * x / (p : Ω) ^ (m + j))) :
    IsInt (p := p) (D (x ^ (p ^ j)) - c * x ^ (p ^ j) / (p : Ω) ^ m) := by
  obtain ⟨k, hk⟩ : ∃ k, p ^ j = k + 1 := ⟨p ^ j - 1, (Nat.succ_pred_eq_of_pos (ppow_pos j)).symm⟩
  have h1 := hD.pow hS hx k
  rw [← hk] at h1
  have e : c * x ^ (p ^ j) / (p : Ω) ^ m =
      ((p ^ j : ℕ) : Ω) * x ^ k * (c * x / (p : Ω) ^ (m + j)) := by
    have e1 : x ^ (p ^ j) = x ^ k * x := by rw [hk, pow_succ]
    have e2 : ((p ^ j : ℕ) : Ω) = (p : Ω) ^ j := by push_cast; ring
    rw [e1, e2, pow_add]
    field_simp
  refine int_congr (int_add h1 (int_mul (int_mul (int_nat (p ^ j)) (int_pow (hS x hx) k)) h)) ?_
  linear_combination (-1 : Ω) * e

theorem compat_gen (T : Tower p Ω) {m n : ℕ} (hmn : m ≤ n) {D D' : Ω → Ω}
    (hD : GlobalTheory.KumDlog.IsDer (Lev T n) D) (hD' : GlobalTheory.KumDlog.IsDer (Lev T m) D')
    (hz : IsInt (p := p) (D (T.ζ m) - D' (T.ζ m))) (hq : IsInt (p := p) (D (T.qq m) - D' (T.qq m))) :
    ∀ x ∈ Lev T m, IsInt (p := p) (D x - D' x) :=
  GlobalTheory.KumDlog.IsDer.adjoin (t := {T.ζ m, T.qq m}) (GlobalTheory.KumDlog.IsDer.sub (hD.mono (Lev_mono T hmn)) hD') (Lev_int T m)
    (by rintro x (rfl | rfl); exacts [zeta_mem_Lev T m, qq_mem_Lev T m])
    (by rintro x (rfl | rfl); exacts [hz, hq])

theorem vals_down (T : Tower p Ω) (hp : (p : Ω) ≠ 0) {m n : ℕ} (hmn : m ≤ n) {dz dq : Ω → Ω}
    (hz : GlobalTheory.KumDlog.IsDer (Lev T n) dz) (hq : GlobalTheory.KumDlog.IsDer (Lev T n) dq) (hv : GlobalTheory.KumDlog.Vals T n dz dq) : GlobalTheory.KumDlog.Vals T m dz dq := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hS := Lev_int T (m + j)
  have zm := zeta_mem_Lev T (m + j)
  have qm := qq_mem_Lev T (m + j)
  have z0 : ∀ {D : Ω → Ω} {x : Ω}, IsInt (p := p) (D x) → IsInt (p := p) (D x - 0 * x / (p : Ω) ^ (m + j)) :=
    fun h => int_congr h (by ring)
  have z1 : ∀ {D : Ω → Ω} {y : Ω}, IsInt (p := p) (D y - 0 * y / (p : Ω) ^ m) → IsInt (p := p) (D y) :=
    fun h => int_congr h (by ring)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := der_pow_val hz hS hp zm hv.1
    rwa [zeta_pow] at this
  · have := z1 (der_pow_val hz hS hp qm (z0 hv.2.1))
    rwa [qq_pow] at this
  · have := z1 (der_pow_val hq hS hp zm (z0 hv.2.2.1))
    rwa [zeta_pow] at this
  · have := der_pow_val hq hS hp qm hv.2.2.2
    rwa [qq_pow] at this

theorem glue_fam (T : Tower p Ω) (F : ℕ → Ω → Ω) (hF : ∀ m, GlobalTheory.KumDlog.IsDer (Lev T (m + 1)) (F m))
    (hc : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt (p := p) (F n x - F m x)) :
    ∃ G : Ω → Ω, (∀ m, ∀ x ∈ Lev T (m + 1), IsInt (p := p) (G x - F m x)) ∧
      ∀ S : Subalgebra (O0 p) Ω, (∀ x ∈ S, ∃ m, x ∈ Lev T m) → GlobalTheory.KumDlog.IsDer S G := by
  classical
  let M : Ω → ℕ := fun x => if h : ∃ m, x ∈ Lev T (m + 1) then Classical.choose h else 0
  have hG : ∀ m, ∀ x ∈ Lev T (m + 1), IsInt (p := p) (F (M x) x - F m x) := by
    intro m x hx
    have h : ∃ m, x ∈ Lev T (m + 1) := ⟨m, hx⟩
    have hM : M x = Classical.choose h := dif_pos h
    have ha := Classical.choose_spec h
    rw [hM]
    have h1 := hc _ (max m (Classical.choose h)) (le_max_right _ _) x ha
    have h2 := hc _ (max m (Classical.choose h)) (le_max_left _ _) x hx
    exact int_congr (int_sub h2 h1) (by ring)
  refine ⟨fun x => F (M x) x, hG, fun S hS => ?_⟩
  have two : ∀ x ∈ S, ∀ y ∈ S, ∃ n, x ∈ Lev T (n + 1) ∧ y ∈ Lev T (n + 1) := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := hS x hx
    obtain ⟨b, hb⟩ := hS y hy
    exact ⟨a + b, Lev_mono T (by omega) ha, Lev_mono T (by omega) hb⟩
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
  · obtain ⟨n, hxn, hyn⟩ := two x hx y hy
    refine int_congr (int_add (int_add (int_sub (int_sub ((hF n).1 x hxn y hyn)
      (hG n x hxn)) (hG n y hyn)) (hG n _ (add_mem hxn hyn))) int_zero) ?_
    ring
  · obtain ⟨n, hxn, hyn⟩ := two x hx y hy
    have ix := Lev_int T _ x hxn
    have iy := Lev_int T _ y hyn
    refine int_congr (int_sub (int_sub (int_add ((hF n).2.1 x hxn y hyn)
      (hG n _ (mul_mem hxn hyn))) (int_mul ix (hG n y hyn))) (int_mul iy (hG n x hxn))) ?_
    ring
  · have hm := (Lev T (0 + 1)).algebraMap_mem c
    exact int_congr (int_add (hG 0 _ hm) ((hF 0).2.2 c)) (by ring)

theorem glue : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (B : Subalgebra (O0 p) Ω), (∀ x ∈ B, ∃ m : ℕ, x ∈ Lev T m) →
    (∀ m : ℕ, 1 ≤ m → ∃ dz dq : Ω → Ω, GlobalTheory.KumDlog.IsDer (Lev T m) dz ∧ GlobalTheory.KumDlog.IsDer (Lev T m) dq ∧ GlobalTheory.KumDlog.Vals T m dz dq) →
    ∃ dz dq : Ω → Ω, GlobalTheory.KumDlog.IsDer B dz ∧ GlobalTheory.KumDlog.IsDer B dq ∧ ∀ m : ℕ, 1 ≤ m → GlobalTheory.KumDlog.Vals T m dz dq := by
  intro p _ Ω _ _ hclo T B hB hlev
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hclo
  have hp : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h' : ∀ m : ℕ, ∃ dz dq : Ω → Ω, GlobalTheory.KumDlog.IsDer (Lev T (m + 1)) dz ∧ GlobalTheory.KumDlog.IsDer (Lev T (m + 1)) dq ∧
      GlobalTheory.KumDlog.Vals T (m + 1) dz dq := fun m => hlev (m + 1) (by omega)
  choose Z Q hZ hQ hV using h'
  have cZ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt (p := p) (Z n x - Z m x) := by
    intro m n hmn
    have v := vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)
    exact compat_gen T (by omega : m + 1 ≤ n + 1) (hZ n) (hZ m)
      (int_congr (int_sub v.1 (hV m).1) (by ring)) (int_congr (int_sub v.2.1 (hV m).2.1) (by ring))
  have cQ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt (p := p) (Q n x - Q m x) := by
    intro m n hmn
    have v := vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)
    exact compat_gen T (by omega : m + 1 ≤ n + 1) (hQ n) (hQ m)
      (int_congr (int_sub v.2.2.1 (hV m).2.2.1) (by ring))
      (int_congr (int_sub v.2.2.2 (hV m).2.2.2) (by ring))
  obtain ⟨dz, hdz, hdzB⟩ := glue_fam T Z hZ cZ
  obtain ⟨dq, hdq, hdqB⟩ := glue_fam T Q hQ cQ
  refine ⟨dz, dq, hdzB B hB, hdqB B hB, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have v := hV k
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact int_congr (int_add (hdz k _ (zeta_mem_Lev T _)) v.1) (by ring)
  · exact int_congr (int_add (hdz k _ (qq_mem_Lev T _)) v.2.1) (by ring)
  · exact int_congr (int_add (hdq k _ (zeta_mem_Lev T _)) v.2.2.1) (by ring)
  · exact int_congr (int_add (hdq k _ (qq_mem_Lev T _)) v.2.2.2) (by ring)

end GlobalTheory.LevGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleEquivariantProjection
section
namespace GlobalTheory.AdmissibleProjection

open GlobalTheory.UnitarySemisimple

variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]

def stab (ρ : Representation ℂ H W) (v : W) : Subgroup H where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := rho_inv_rho ρ a v

theorem orbit_finite [TopologicalSpace H] [IsTopologicalGroup H] (ρ : Representation ℂ H W)
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w}) (K : Subgroup H) (hK : IsCompact (K : Set H))
    (w : W) : (Set.range fun k : K => ρ k w).Finite := by
  have hopen : ∀ i : K, IsOpen {h : H | ρ h w = ρ (i : H) w} := by
    intro i
    have e : {h : H | ρ h w = ρ (i : H) w} = (fun h => (i : H)⁻¹ * h) ⁻¹' {h | ρ h w = w} := by
      ext h
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, Module.End.mul_apply]
      constructor
      · intro e; rw [e, rho_inv_rho]
      · intro e
        calc ρ h w = ρ (i : H) (ρ (i : H)⁻¹ (ρ h w)) := (rho_rho_inv ρ _ _).symm
          _ = ρ (i : H) w := by rw [e]
    rw [e]
    exact (hsm w).preimage (continuous_const_mul _)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : K => {h : H | ρ h w = ρ (i : H) w}) hopen
    (fun h hh => Set.mem_iUnion.2 ⟨⟨h, hh⟩, rfl⟩)
  refine (t.finite_toSet.image (fun i : K => ρ (i : H) w)).subset ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht k.2)
  exact ⟨i, hi, hki.symm⟩

theorem hadm_of [TopologicalSpace H] [IsTopologicalGroup H] (ρ : Representation ℂ H W)
    (hK0 : ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H))
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w})
    (hfd : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K)) :
    ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite := by
  obtain ⟨K₀, hop, hco⟩ := hK0
  intro v
  refine ⟨K₀ ⊓ stab ρ v, fun k hk => hk.2, hfd _ ?_, fun w => ?_⟩
  · rw [Subgroup.coe_inf]; exact hop.inter (hsm v)
  · refine (orbit_finite ρ hsm K₀ hco w).subset ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨k, k.2.1⟩, rfl⟩

theorem exists_proj (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hdef : ∀ v, B v v = 0 → v = 0) (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hadm : ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite)
    (Z : Subrepresentation ρ) :
    ∃ P : W →ₗ[ℂ] W, (∀ w, P w ∈ Z.toSubmodule) ∧ (∀ w, ∀ z ∈ Z.toSubmodule, B z (w - P w) = 0) ∧
      ∀ g w, P (ρ g w) = ρ g (P w) := by
  classical
  have hex := fun w => exists_compl_proj ρ B hdef hinv hadm Z w
  let f : W → W := fun w => Classical.choose (hex w)
  have hf1 : ∀ w, f w ∈ Z.toSubmodule := fun w => (Classical.choose_spec (hex w)).1
  have hf2 : ∀ w, ∀ z ∈ Z.toSubmodule, B z (w - f w) = 0 :=
    fun w => (Classical.choose_spec (hex w)).2
  have huniq : ∀ w t, t ∈ Z.toSubmodule → (∀ z ∈ Z.toSubmodule, B z (w - t) = 0) → f w = t := by
    intro w t ht htw
    have hd : f w - t ∈ Z.toSubmodule := sub_mem (hf1 w) ht
    have h0 : B (f w - t) (f w - t) = 0 := by
      calc B (f w - t) (f w - t) = B (f w - t) ((w - t) - (w - f w)) := by congr 1; abel
        _ = 0 := by rw [map_sub, htw _ hd, hf2 w _ hd, sub_zero]
    exact sub_eq_zero.1 (hdef _ h0)
  let P : W →ₗ[ℂ] W :=
    { toFun := f
      map_add' := fun a b => huniq _ _ (add_mem (hf1 a) (hf1 b)) (fun z hz => by
        rw [show a + b - (f a + f b) = (a - f a) + (b - f b) by abel, map_add (f := _), hf2 a z hz,
          hf2 b z hz, add_zero])
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        exact huniq _ _ (Z.toSubmodule.smul_mem c (hf1 a)) (fun z hz => by
          rw [← smul_sub, map_smul, hf2 a z hz, smul_zero]) }
  refine ⟨P, hf1, hf2, fun g w => ?_⟩
  exact huniq _ _ (Z.apply_mem_toSubmodule g (hf1 w)) (fun z hz => by
    rw [← map_sub]; exact orth_stable ρ B hinv Z (w - f w) (hf2 w) g z hz)

theorem exists_irreducible_equivariant_projection : ∀ (H W : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ u v, star (B u v) = B v u) → (∀ v, 0 ≤ (B v v).re) → (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (ρ g u) (ρ g v) = B u v) → (∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H)) → (∀ w, IsOpen {k : H | ρ k w = w}) → (∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K)) → ∀ x : W, x ≠ 0 → ∃ (U : Submodule ℂ W) (P : W →ₗ[ℂ] W), U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) ∧ (∀ w, P w ∈ U) ∧ (∀ g w, P (ρ g w) = ρ g (P w)) ∧ P x ≠ 0 := by
  intro H W _ _ _ _ _ ρ B hherm hpos hdef hinv hK0 hsm hfd x hx
  classical
  have hadm := hadm_of ρ hK0 hsm hfd
  obtain ⟨K0, hxK, hfdK, -⟩ := hadm x
  set F := GlobalTheory.PRep.fixed ρ K0 with hF
  haveI := hfdK
  have ofF : ∀ u ∈ F, ∀ k ∈ K0, ρ k u = u := by
    intro u hu k hk
    have := hu ⟨k, hk⟩
    simpa using this
  have memF : ∀ u, (∀ k ∈ K0, ρ k u = u) → u ∈ F := by
    intro u hu k
    show ρ (k : H) u = ((1 : ℂˣ) : ℂ) • u
    simp [hu k k.2]
  set O := (orbSpan ρ x).toSubmodule with hO
  let Q : W → Prop := fun y => y ≠ 0 ∧ y ∈ F ∧ y ∈ O
  have hex : ∃ n : ℕ, ∃ y, Q y ∧
      Module.finrank ℂ ((orbSpan ρ y).toSubmodule ⊓ F : Submodule ℂ W) = n :=
    ⟨_, x, ⟨hx, memF x hxK, mem_orbSpan ρ x⟩, rfl⟩
  obtain ⟨y, ⟨hy0, hyF, hyO⟩, hn⟩ := Nat.find_spec hex
  have hmin : ∀ t, Q t → Module.finrank ℂ ((orbSpan ρ y).toSubmodule ⊓ F : Submodule ℂ W) ≤
      Module.finrank ℂ ((orbSpan ρ t).toSubmodule ⊓ F : Submodule ℂ W) := by
    intro t ht
    rw [hn]
    exact Nat.find_min' hex ⟨t, ht, rfl⟩
  set U := orbSpan ρ y with hU
  have hyU : y ∈ U.toSubmodule := mem_orbSpan ρ y
  have hUO : U.toSubmodule ≤ O := orbSpan_le ρ y (orbSpan ρ x) hyO
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_proj ρ B hdef hinv hadm U
  refine ⟨U.toSubmodule, P, ?_, fun g u hu => U.apply_mem_toSubmodule g hu, ?_, hP1, hP3, ?_⟩
  · intro h
    apply hy0
    rw [h] at hyU
    exact (Submodule.mem_bot ℂ).1 hyU
  · intro N hNU hN
    let N' : Subrepresentation ρ := ⟨N, by intro g v hv; exact hN g v hv⟩
    obtain ⟨t, htN, ht⟩ := exists_compl_proj ρ B hdef hinv hadm N' y
    have hfix : ∀ g, ρ g y = y → ρ g t = t := by
      intro g hg
      have h1 : ρ g t - t ∈ N'.toSubmodule := sub_mem (N'.apply_mem_toSubmodule g htN) htN
      have h2 : ∀ z ∈ N'.toSubmodule, B z (ρ g t - t) = 0 := by
        intro z hz
        have e : ρ g t - t = (y - t) - ρ g (y - t) := by
          rw [map_sub, hg]
          abel
        rw [e, map_sub, ht z hz, orth_stable ρ B hinv N' _ ht g z hz, sub_zero]
      exact sub_eq_zero.1 (hdef _ (h2 _ h1))
    by_cases ht0 : t = 0
    · left
      have hyo : ∀ z ∈ N'.toSubmodule, B z y = 0 := by
        intro z hz
        simpa [ht0] using ht z hz
      have hUo : ∀ z ∈ N'.toSubmodule, ∀ u ∈ U.toSubmodule, B z u = 0 := by
        intro z hz u hu
        have hle : U.toSubmodule ≤ LinearMap.ker (B z) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨g, rfl⟩
          exact orth_stable ρ B hinv N' y hyo g z hz
        exact hle hu
      rw [Submodule.eq_bot_iff]
      intro v hv
      exact hdef _ (hUo _ hv _ (hNU hv))
    · right
      have hQt : Q t := ⟨ht0, memF t (fun k hk => hfix k (ofF y hyF k hk)), hUO (hNU htN)⟩
      have h1 := hmin t hQt
      haveI : FiniteDimensional ℂ (U.toSubmodule ⊓ F : Submodule ℂ W) :=
        Submodule.finiteDimensional_of_le inf_le_right
      haveI : FiniteDimensional ℂ (N ⊓ F : Submodule ℂ W) :=
        Submodule.finiteDimensional_of_le inf_le_right
      have hle1 : ((orbSpan ρ t).toSubmodule ⊓ F : Submodule ℂ W) ≤ N ⊓ F :=
        inf_le_inf_right _ (orbSpan_le ρ t N' htN)
      have hle2 : (N ⊓ F : Submodule ℂ W) ≤ U.toSubmodule ⊓ F := inf_le_inf_right _ hNU
      have h2 := LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle1)
        (Submodule.inclusion_injective hle1)
      have heq := Submodule.eq_of_le_of_finrank_le hle2 (h1.trans h2)
      have hyN : y ∈ N := by
        have : y ∈ (N ⊓ F : Submodule ℂ W) := heq ▸ ⟨hyU, hyF⟩
        exact this.1
      exact le_antisymm hNU (orbSpan_le ρ y N' hyN)
  · intro hPx
    have hxo : ∀ z ∈ U.toSubmodule, B z x = 0 := by
      intro z hz
      simpa [hPx] using hP2 x z hz
    have hle : O ≤ LinearMap.ker (B y) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      exact orth_stable ρ B hinv U x hxo g y hyU
    exact hy0 (hdef _ (hle (hUO hyU)))

end GlobalTheory.AdmissibleProjection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearLimitOfCompatibleFamily
section
open Filter Topology

namespace GlobalTheory

theorem exists_baseChange_extension_of_flat {A K E M : Type*} [CommRing A] [Field K] [Algebra A K]
    [Module.Flat A K] [AddCommGroup E] [Module K E] [AddCommGroup M] [Module A M]
    (B : Submodule A M) (Θ : B → E)
    (h : ∀ (a a' : A) (b b' : B),
      Θ (a • b + a' • b') = algebraMap A K a • Θ b + algebraMap A K a' • Θ b') :
    ∃ L : TensorProduct A K M →ₗ[K] E, ∀ b : B, L (1 ⊗ₜ[A] (b : M)) = Θ b := by
  letI : Module A E := Module.compHom E (algebraMap A K)
  have hs : ∀ (a : A) (e : E), a • e = algebraMap A K a • e := fun _ _ => rfl
  haveI : IsScalarTower A K E := ⟨fun a k e => by rw [hs, Algebra.smul_def, mul_smul]⟩
  let Θ' : B →ₗ[A] E :=
    { toFun := Θ
      map_add' := fun b b' => by simpa using h 1 1 b b'
      map_smul' := fun a b => by
        have := h a 0 b b
        rwa [zero_smul, add_zero, map_zero, zero_smul, add_zero] at this }
  have hinj : Function.Injective (B.subtype.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ B.injective_subtype
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (B.subtype.baseChange K)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(Θ'.liftBaseChange K).comp r, fun b => ?_⟩
  have h1 : r (1 ⊗ₜ[A] (b : M)) = 1 ⊗ₜ[A] b := by
    simpa using LinearMap.congr_fun hr (1 ⊗ₜ[A] b)
  rw [LinearMap.comp_apply, h1, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

theorem tendsto_appr_padicComplex (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) :
    Tendsto (fun n => (((a.appr n : ℕ) : PadicAlgCl l) : ℂ_[l])) atTop
      (𝓝 ((algebraMap ℤ_[l] (PadicAlgCl l) a : PadicAlgCl l) : ℂ_[l])) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hq : ‖(l : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq)
  have hn : ∀ z : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ = ‖z‖ := fun z =>
    PadicAlgCl.norm_extends l (z : ℚ_[l])
  rw [← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℤ_[l] (PadicAlgCl l)), ← map_sub, hn, norm_sub_rev]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n a)
  rw [← ht, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) t.norm_le_one

theorem exists_linear_limit_of_compatible_family :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M)
      (R : ℕ → M → PadicAlgCl l → Prop) (C : ℝ),
    (∀ n, ∀ b ∈ B, ∃ x, R n b x) →
    (∀ n, ∀ b ∈ B, ∀ x y, R (n + 1) b x → R n b y →
      ‖x - y‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖) →
    (∀ n, ∀ b ∈ B, ∀ b' ∈ B, ∀ (a a' : ℤ_[l]) (x x' : PadicAlgCl l), R n b x → R n b' x' →
      R n (a • b + a' • b')
        (((a.appr n : ℕ) : PadicAlgCl l) * x + ((a'.appr n : ℕ) : PadicAlgCl l) * x')) →
    ∃ L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l], ∀ n, ∀ b ∈ B, ∀ x,
      R n b x → ‖(x : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖ := by
  intro l _ M _ _ B R C h1 h2 h3
  simp only [norm_pow] at h2 ⊢
  set q : ℝ := ‖((l : ℕ) : PadicAlgCl l)‖ with hqdef
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq1 : q < 1 := by
    rw [hqdef, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  choose! x hx using h1
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans
      (h2 0 0 B.zero_mem _ _ (hx 1 0 B.zero_mem) (hx 0 0 B.zero_mem))
    simpa using this
  have hmono : ∀ {n m : ℕ}, n ≤ m → C * q ^ m ≤ C * q ^ n := fun h =>
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1.le h) hC
  have htail : ∀ n, ∀ b ∈ B, ∀ y, R n b y → ∀ m, n + 1 ≤ m → ‖x m b - y‖ ≤ C * q ^ n := by
    intro n b hb y hy m hm
    induction m, hm using Nat.le_induction with
    | base => exact h2 n b hb _ _ (hx _ b hb) hy
    | succ m hm ih =>
      have e : x (m + 1) b - y = (x (m + 1) b - x m b) + (x m b - y) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (h2 m b hb _ _ (hx _ b hb) (hx _ b hb)).trans (hmono (by omega))
  have hlim : ∀ b : B, ∃ z : ℂ_[l], Tendsto (fun n => ((x n b : PadicAlgCl l) : ℂ_[l])) atTop (𝓝 z) := by
    intro b
    refine cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric q C hq1 fun n => ?_)
    rw [dist_eq_norm, ← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends, norm_sub_rev]
    exact h2 n b b.2 _ _ (hx _ _ b.2) (hx _ _ b.2)
  choose Θ hΘ using hlim
  have hbound : ∀ n (b : B) (y : PadicAlgCl l), R n b y → ‖(y : ℂ_[l]) - Θ b‖ ≤ C * q ^ n := by
    intro n b y hy
    refine le_of_tendsto ((tendsto_const_nhds (x := (y : ℂ_[l]))).sub (hΘ b)).norm
      (eventually_atTop.2 ⟨n + 1, fun m hm => ?_⟩)
    rw [← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends, norm_sub_rev]
    exact htail n b b.2 y hy m hm
  haveI : Module.Flat ℤ_[l] ℚ_[l] := IsLocalization.flat ℚ_[l] (nonZeroDivisors ℤ_[l])
  haveI : Module.Flat ℤ_[l] (PadicAlgCl l) := Module.Flat.trans ℤ_[l] ℚ_[l] (PadicAlgCl l)
  obtain ⟨L, hL⟩ := exists_baseChange_extension_of_flat (K := PadicAlgCl l) B Θ (by
    intro a a' b b'
    have hA := ((tendsto_appr_padicComplex l a).mul (hΘ b)).add
      ((tendsto_appr_padicComplex l a').mul (hΘ b'))
    rw [Algebra.smul_def, Algebra.smul_def]
    refine tendsto_nhds_unique ?_ hA
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun n : ℕ => C * q ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have := hbound n (a • b + a' • b') _
      (h3 n b b.2 b' b'.2 a a' _ _ (hx n _ b.2) (hx n _ b'.2))
    rwa [UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_mul,
      UniformSpace.Completion.coe_mul] at this)
  refine ⟨L, fun n b hb y hy => ?_⟩
  rw [show L (1 ⊗ₜ[ℤ_[l]] b) = Θ ⟨b, hb⟩ from hL ⟨b, hb⟩]
  exact hbound n ⟨b, hb⟩ y hy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulLinearIndependentAlgebraicOverPadicInte
section
open GlobalTheory.K5

namespace GlobalTheory.K5.ReprInd

theorem aux {R Ω : Type*} [CommRing R] [IsDomain R] [AddCommGroup Ω] [Module R Ω] (P : Ω → Prop) :
    ∀ (m : ℕ) (a : Fin m → Ω) (f : Fin m → R), (∀ i, P (a i)) →
      ∃ (n : ℕ) (a' : Fin n → Ω) (f' : Fin n → R) (g : R), (∀ i, P (a' i)) ∧
        LinearIndependent R a' ∧ g ≠ 0 ∧ g • (∑ i, f i • a i) = ∑ i, f' i • a' i := by
  intro m
  induction m with
  | zero =>
    intro a f _
    refine ⟨0, a, f, 1, by simp, linearIndependent_empty_type, one_ne_zero, by simp⟩
  | succ m ih =>
    intro a f hP
    by_cases hli : LinearIndependent R a
    · exact ⟨m + 1, a, f, 1, hP, hli, one_ne_zero, one_smul _ _⟩
    · obtain ⟨c, hc, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hli
      obtain ⟨n, a', f', g, hP', hli', hg, heq⟩ := ih (fun j => a (k.succAbove j))
        (fun j => c k * f (k.succAbove j) - f k * c (k.succAbove j)) (fun j => hP _)
      refine ⟨n, a', f', g * c k, hP', hli', mul_ne_zero hg hk, ?_⟩
      have key : c k • (∑ i, f i • a i) =
          ∑ j : Fin m, (c k * f (k.succAbove j) - f k * c (k.succAbove j)) • a (k.succAbove j) := by
        have h1 : c k • (∑ i, f i • a i) = c k • (∑ i, f i • a i) - f k • (∑ i, c i • a i) := by
          rw [hc, smul_zero, sub_zero]
        rw [h1, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
          Fin.sum_univ_succAbove _ k]
        simp only [smul_smul, ← sub_smul]
        rw [mul_comm (f k) (c k), sub_self, zero_smul, zero_add]
      rw [mul_smul, key, heq]

theorem main {R Ω : Type*} [CommRing R] [IsDomain R] [Field Ω] [Algebra R Ω] (P : Ω → Prop) :
    ∀ y ∈ Submodule.span R {x : Ω | P x},
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → R) (g : R), (∀ i, P (a i)) ∧
      LinearIndependent R a ∧ g ≠ 0 ∧
      algebraMap R Ω g * y = ∑ i, algebraMap R Ω (f i) * a i := by
  intro y hy
  obtain ⟨m, f, a, rfl⟩ := Submodule.mem_span_set'.mp hy
  obtain ⟨n, a', f', g, hP', hli', hg, heq⟩ := aux P m (fun i => (a i : Ω)) f (fun i => (a i).2)
  refine ⟨n, a', f', g, hP', hli', hg, ?_⟩
  simpa only [Algebra.smul_def] using heq

end GlobalTheory.K5.ReprInd

theorem GlobalTheory.K5.algSpan_reprInd : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ y ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp (p := p) x},
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → O0 p) (g : O0 p), (∀ i, IsAlgZp (p := p) (a i)) ∧
      LinearIndependent (O0 p) a ∧ g ≠ 0 ∧
      algebraMap (O0 p) Ω g * y = ∑ i, algebraMap (O0 p) Ω (f i) * a i := by
  intro p _ Ω _ _ _
  exact GlobalTheory.K5.ReprInd.main (fun x => IsAlgZp (p := p) x)
end

