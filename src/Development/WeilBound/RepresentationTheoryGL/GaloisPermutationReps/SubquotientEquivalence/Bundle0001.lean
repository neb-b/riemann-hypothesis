module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.EquivariantPartsOfFiniteType
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

lemma pow_pow_pow_add (z : ℂ) (q a b : ℕ) : (z ^ q ^ a) ^ q ^ b = z ^ q ^ (a + b) := by
  rw [← pow_mul, ← pow_add]

lemma eigenvector_maps_power {V : Type} [AddCommGroup V] [Module ℂ V] (q : ℕ) (M G : Module.End ℂ V)
    (hMG : M * G = G * M ^ q) (z : ℂ) (v : V) (hv : M v = z • v) : M (G v) = z ^ q • G v := by
  have hpow : ∀ k : ℕ, (M ^ k) v = z ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
  have h := congrArg (fun T : Module.End ℂ V => T v) hMG
  simp only [Module.End.mul_apply] at h
  rw [h, hpow, map_smul]

lemma eigenvector_iterate_power {V : Type} [AddCommGroup V] [Module ℂ V] (q : ℕ) (M G : Module.End ℂ V)
    (hMG : M * G = G * M ^ q) (z : ℂ) (v : V) (hv : M v = z • v) :
    ∀ i : ℕ, M ((G ^ i) v) = z ^ q ^ i • (G ^ i) v := by
  intro i
  induction i with
  | zero => simpa using hv
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, eigenvector_maps_power q M G hMG _ _ ih, ← pow_mul, ← pow_succ]

theorem st1a : St1a := by
  classical
  intro V _ _ _ q M G hM hG hMG hirr
  obtain ⟨hnt, hU⟩ := hirr
  have hGinj : ∀ i : ℕ, Function.Injective (G ^ i) := fun i =>
    ((Module.End.isUnit_iff _).mp (hG.pow i)).1
  have hMinj : Function.Injective M := ((Module.End.isUnit_iff _).mp hM).1
  have hfin : Set.Finite {μ | M.HasEigenvalue μ} := M.finite_hasEigenvalue
  have hstep : ∀ μ, M.HasEigenvalue μ → M.HasEigenvalue (μ ^ q) := by
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hv' : M v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := G v) ⟨?_, ?_⟩
    · exact Module.End.mem_eigenspace_iff.mpr (eigenvector_maps_power q M G hMG μ v hv')
    · intro h0
      apply hv.2
      have h1 := hGinj 1
      rw [pow_one] at h1
      exact h1 (by rw [h0, map_zero])
  obtain ⟨z0, hz0⟩ := M.exists_eigenvalue
  have hall : ∀ i : ℕ, M.HasEigenvalue (z0 ^ q ^ i) := by
    intro i
    induction i with
    | zero => simpa using hz0
    | succ i ih =>
      have h := hstep _ ih
      rwa [← pow_mul, ← pow_succ] at h
  obtain ⟨a, b, hab, heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun i : ℕ => z0 ^ q ^ i) (t := {μ | M.HasEigenvalue μ}) (fun i => hall i) hfin
  have hzE : M.HasEigenvalue (z0 ^ q ^ a) := hall a
  have hper : (z0 ^ q ^ a) ^ q ^ (b - a) = z0 ^ q ^ a := by
    rw [pow_pow_pow_add, show a + (b - a) = b by omega, ← heq]
  generalize z0 ^ q ^ a = z at hzE hper
  have hP : ∃ e : ℕ, 0 < e ∧ z ^ q ^ e = z := ⟨b - a, by omega, hper⟩
  obtain ⟨d, ⟨hd0, hzd⟩, hdmin⟩ : ∃ d : ℕ, (0 < d ∧ z ^ q ^ d = z) ∧
      ∀ e < d, ¬ (0 < e ∧ z ^ q ^ e = z) :=
    ⟨Nat.find hP, Nat.find_spec hP, fun e he => Nat.find_min hP he⟩

  have hmaps : ∀ x ∈ M.eigenspace z, (G ^ d) x ∈ M.eigenspace z := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [eigenvector_iterate_power q M G hMG z x hx d, hzd]
  have hne : M.eigenspace z ≠ ⊥ := hzE
  have : Nontrivial (M.eigenspace z) := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (LinearMap.restrict (G ^ d) hmaps)
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hw1 : LinearMap.restrict (G ^ d) hmaps w = μ • w := Module.End.mem_eigenspace_iff.mp hw.1
  set v : V := (w : V) with hv_def
  have hGd : (G ^ d) v = μ • v := by
    have h := congrArg Subtype.val hw1
    simpa [LinearMap.restrict_apply] using h
  have hvE : M v = z • v := Module.End.mem_eigenspace_iff.mp w.2
  have hv0 : v ≠ 0 := by
    intro h
    apply hw.2
    exact Subtype.ext h

  let bb : Fin d → V := fun i => (G ^ (i : ℕ)) v
  have hb_eig : ∀ i : Fin d, M (bb i) = z ^ q ^ (i : ℕ) • bb i := fun i =>
    eigenvector_iterate_power q M G hMG z v hvE i
  have hb_ne : ∀ i : Fin d, bb i ≠ 0 := by
    intro i h
    apply hv0
    exact hGinj i (by rw [map_zero]; exact h)
  have key : ∀ i j : ℕ, i < j → j < d → z ^ q ^ i = z ^ q ^ j → False := by
    intro i j hij hjd hij'
    have h1 : z ^ q ^ (j - i) = z := by
      calc z ^ q ^ (j - i) = (z ^ q ^ d) ^ q ^ (j - i) := by rw [hzd]
        _ = (z ^ q ^ j) ^ q ^ (d - i) := by
          rw [pow_pow_pow_add, pow_pow_pow_add, show j + (d - i) = d + (j - i) by omega]
        _ = (z ^ q ^ i) ^ q ^ (d - i) := by rw [hij']
        _ = z ^ q ^ d := by rw [pow_pow_pow_add, show i + (d - i) = d by omega]
        _ = z := hzd
    exact hdmin (j - i) (by omega) ⟨by omega, h1⟩
  have hinj : Function.Injective (fun i : Fin d => z ^ q ^ (i : ℕ)) := by
    intro i j hij
    simp only at hij
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
    · exact (key i j h j.2 hij).elim
    · exact Fin.ext h
    · exact (key j i h i.2 hij.symm).elim
  have hli : LinearIndependent ℂ bb :=
    Module.End.eigenvectors_linearIndependent' M (fun i : Fin d => z ^ q ^ (i : ℕ)) hinj bb
      (fun i => ⟨Module.End.mem_eigenspace_iff.mpr (hb_eig i), hb_ne i⟩)
  set W : Submodule ℂ V := Submodule.span ℂ (Set.range bb) with hW_def
  have hvW : v ∈ W := Submodule.subset_span ⟨⟨0, hd0⟩, by simp [bb]⟩
  have hMW : ∀ x ∈ W, M x ∈ W := by
    have hle : W ≤ W.comap M := by
      rw [hW_def, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, hb_eig i]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact fun x hx => hle hx
  have hGW : ∀ x ∈ W, G x ∈ W := by
    have hle : W ≤ W.comap G := by
      rw [hW_def, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      show G ((G ^ (i : ℕ)) v) ∈ W
      rw [← Module.End.mul_apply, ← pow_succ']
      by_cases h : (i : ℕ) + 1 < d
      · exact Submodule.subset_span ⟨⟨(i : ℕ) + 1, h⟩, rfl⟩
      · rw [show (i : ℕ) + 1 = d by omega, hGd]
        exact Submodule.smul_mem _ _ hvW
    exact fun x hx => hle hx
  have hWtop : W = ⊤ := by
    rcases hU W hMW hGW with h | h
    · exfalso
      apply hv0
      have := hvW
      rw [h] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exact h
  have hfr : Module.finrank ℂ V = d := by
    have h := finrank_span_eq_card hli
    rw [← hW_def, hWtop, finrank_top, Fintype.card_fin] at h
    exact h
  refine ⟨z, hzE, ?_⟩
  rw [hfr]
  refine ⟨?_, hzd, fun e he0 hed h => hdmin e hed ⟨he0, h⟩⟩
  intro hz
  apply hv0
  apply hMinj
  rw [hvE, hz, zero_smul, map_zero]

end PositivityTheory.Rg.DzCount

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ExistsLiftUnipotentRadical
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

namespace L5

section Entries

variable {R : Type} [CommRing R] {s N : ℕ} {d : Fin s → ℕ} {e : (Σ a, Fin (d a)) ≃ Fin N}

theorem mem_unipotent_radical_iff_alt {u : GL (Fin N) R} :
    u ∈ unipRad R e ↔
      ∀ i j, ¬ blk e i < blk e j → (u : Matrix (Fin N) (Fin N) R) i j = (1 : Matrix (Fin N) (Fin N) R) i j := by
  rw [mem_unipRad, mem_parab]
  constructor
  · rintro ⟨hP, hD⟩ i j hij
    rcases lt_or_eq_of_le (not_lt.1 hij) with h | h
    · rw [hP i j h, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ h
    · obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective j
      simp only [blk_apply] at h
      subst h
      rw [hD, Matrix.one_apply, Matrix.one_apply]
      simp [e.apply_eq_iff_eq]
  · intro h
    refine ⟨fun i j hij => ?_, fun a p q => ?_⟩
    · rw [h i j (not_lt.2 hij.le), Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hij
    · rw [h _ _ (by simp), Matrix.one_apply, Matrix.one_apply]
      simp [e.apply_eq_iff_eq]

theorem exists_block_lt_of_ne_bot (h : unipRad R e ≠ ⊥) : ∃ i j, blk e i < blk e j := by
  by_contra hc
  push Not at hc
  apply h
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_one]
  exact (mem_unipotent_radical_iff_alt.1 hu) i j (not_lt.2 (hc i j))

theorem unipotent_radical_ne_bot {K : Type} [Field K] (h : ∃ i j, blk e i < blk e j) : unipRad K e ≠ ⊥ := by
  obtain ⟨i, j, hij⟩ := h
  have hne : i ≠ j := by
    rintro rfl
    exact lt_irrefl _ hij
  let t : GL (Fin N) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j 1)
    (by rw [Matrix.det_transvection_of_ne _ _ hne]; exact one_ne_zero)
  have ht : t ∈ unipRad K e := by
    rw [mem_unipotent_radical_iff_alt]
    intro a b hab
    show (1 + Matrix.single i j (1 : K)) a b = _
    rw [Matrix.add_apply, Matrix.single_apply, ite_eq_right, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hab hij
  intro hb
  rw [hb, Subgroup.mem_bot] at ht
  have h1 := congrArg (fun x : GL (Fin N) K => (x : Matrix (Fin N) (Fin N) K) i j) ht
  simp only [t, Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_one] at h1
  change (1 + Matrix.single i j (1 : K)) i j = (1 : Matrix (Fin N) (Fin N) K) i j at h1
  rw [Matrix.add_apply, Matrix.single_apply_same, Matrix.one_apply_ne hne, zero_add] at h1
  exact one_ne_zero h1

end Entries

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s N : ℕ} {d : Fin s → ℕ} {e : (Σ a, Fin (d a)) ≃ Fin N}

theorem exists_lift_unipotent_radical (u : GL (Fin N) 𝓀[k]) (hu : u ∈ unipRad 𝓀[k] e) :
    ∃ g : KO k (Fin N), redK k (Fin N) g = u ∧ (g : GL (Fin N) k) ∈ unipRad k e := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : 𝓀[k] → 𝒪[k], ∀ x, IsLocalRing.residue 𝒪[k] (r x) = x :=
    ⟨Function.surjInv IsLocalRing.residue_surjective, Function.surjInv_eq IsLocalRing.residue_surjective⟩
  let M : Matrix (Fin N) (Fin N) 𝒪[k] := fun a b =>
    if blk e a < blk e b then r ((u : Matrix (Fin N) (Fin N) 𝓀[k]) a b)
    else (1 : Matrix (Fin N) (Fin N) 𝒪[k]) a b
  have hM : ∀ a b, ¬ blk e a < blk e b → M a b = (1 : Matrix (Fin N) (Fin N) 𝒪[k]) a b := fun a b h => by
    simp only [M, ite_eq_right h]
  have hT : M.BlockTriangular (blk e) := fun a b hab => by
    rw [hM a b (not_lt.2 hab.le), Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hab
  have hdet : M.det = 1 := by
    rw [hT.det_fintype]
    refine Finset.prod_eq_one fun c _ => ?_
    have : M.toSquareBlock (blk e) c = 1 := by
      refine Matrix.ext fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_
      show M x y = _
      rw [hM x y (by rw [hx, hy]; exact lt_irrefl _), Matrix.one_apply, Matrix.one_apply]
      simp [Subtype.ext_iff]
    rw [this, Matrix.det_one]
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hdet]; exact isUnit_one)
  let g : GL (Fin N) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) hU.unit
  have hgK : g ∈ KO k (Fin N) := MonoidHom.mem_range.2 ⟨hU.unit, rfl⟩
  refine ⟨⟨g, hgK⟩, ?_, ?_⟩
  · refine Units.ext (Matrix.ext fun a b => ?_)
    rw [redK_apply]
    show IsLocalRing.residue 𝒪[k] (M a b) = _
    by_cases h : blk e a < blk e b
    · simp only [M, ite_eq_left h, hr]
    · rw [hM a b h, (mem_unipotent_radical_iff_alt.1 hu) a b h, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
  · rw [mem_unipotent_radical_iff_alt]
    intro a b h
    show algebraMap 𝒪[k] k (M a b) = _
    rw [hM a b h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem lift_mem_twisted_kernel {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) 𝓀[k]) W) (ρ : Representation ℂ (GL (Fin N) k) V) (j : W →ₗ[ℂ] V)
    (hj : ∀ (g : KO k (Fin N)) (v : W), j (τ (redK k (Fin N) g) v) = ρ (g : GL (Fin N) k) (j v))
    (hCF : ∀ v : W, (∀ u ∈ unipRad 𝓀[k] e, τ u v = v) → v = 0) (x : W) :
    j x ∈ twKer ρ (unipRad k e) 1 := by
  classical
  have : Finite (GL (Fin N) 𝓀[k]) :=
    Finite.of_injective (fun g : GL (Fin N) 𝓀[k] => fun i j => (g : Matrix (Fin N) (Fin N) 𝓀[k]) i j)
      (fun a b h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j))
  let _ : Fintype (unipRad 𝓀[k] e) := Fintype.ofFinite _
  let y : W := ∑ u : unipRad 𝓀[k] e, τ u x
  have hy : y = 0 := by
    apply hCF
    intro u hu
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, map_sum]
    rw [show (∑ v : unipRad 𝓀[k] e, τ u (τ v x)) =
        ∑ v : unipRad 𝓀[k] e, τ ((⟨u, hu⟩ * v : unipRad 𝓀[k] e) : GL (Fin N) 𝓀[k]) x from
      Finset.sum_congr rfl fun v _ => by rw [Subgroup.coe_mul, map_mul, mul_apply_eq_comp]]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨u, hu⟩ : unipRad 𝓀[k] e)) _ _ fun v => rfl
  choose lf hlf using fun u : unipRad 𝓀[k] e => exists_lift_unipotent_radical (e := e) u.1 u.2
  have hsum : ∑ u : unipRad 𝓀[k] e, (j x - ρ ((lf u : KO k (Fin N)) : GL (Fin N) k) (j x)) ∈
      twKer ρ (unipRad k e) 1 := by
    refine Submodule.sum_mem _ fun u _ => ?_
    have : ρ ((lf u : KO k (Fin N)) : GL (Fin N) k) (j x) - j x ∈ twKer ρ (unipRad k e) 1 :=
      Submodule.subset_span ⟨⟨_, (hlf u).2⟩, j x, by simp⟩
    rw [← neg_sub]
    exact neg_mem this
  have h2 : ∑ u : unipRad 𝓀[k] e, (j x - ρ ((lf u : KO k (Fin N)) : GL (Fin N) k) (j x)) =
      (Fintype.card (unipRad 𝓀[k] e) : ℂ) • j x := by
    rw [Finset.sum_sub_distrib]
    have : ∑ u : unipRad 𝓀[k] e, ρ ((lf u : KO k (Fin N)) : GL (Fin N) k) (j x) = j y := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [y, map_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← hj, (hlf u).1]
    rw [this, hy, map_zero, sub_zero, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  rw [h2] at hsum
  have hc : (Fintype.card (unipRad 𝓀[k] e) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have := (twKer ρ (unipRad k e) 1).smul_mem (Fintype.card (unipRad 𝓀[k] e) : ℂ)⁻¹ hsum
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end Local

end L5


open L5 in
theorem st5 : St5 := by
  intro k W _ _ _ _ _ _ _ n τ hτ π j hj
  refine ⟨π.smooth, fun s d e hne => ?_⟩
  have hCF := hτ s d e (unipotent_radical_ne_bot (exists_block_lt_of_ne_bot hne))
  let S : Submodule ℂ π.V := Submodule.span ℂ {v | ∃ h x, v = π.ρ h (j x)}
  have hSst : ∀ h v, v ∈ S → π.ρ h v ∈ S := by
    intro h v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨h', x, rfl⟩ := hv
      exact Submodule.subset_span ⟨h * h', x, by rw [map_mul, mul_apply_eq_comp]⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hS0 : S ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : W)
    intro hb
    have hm : j x ∈ S := Submodule.subset_span ⟨1, x, by simp⟩
    rw [hb, Submodule.mem_bot] at hm
    exact hx (hj.1 (hm.trans (map_zero j).symm))
  have hST : S ≤ twKer π.ρ (unipRad k e) 1 := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, x, rfl⟩
    obtain ⟨p, w, hw, rfl⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul e h
    rw [map_mul, mul_apply_eq_comp,
      show π.ρ w (j x) = j (τ (redK k (Fin n) ⟨w, hw⟩) x) from (hj.2 ⟨w, hw⟩ x).symm]
    exact twKer_le_comap π.ρ _ p (parab_le_normalizer k e p.2) (lift_mem_twisted_kernel τ π.ρ j hj.2 hCF _)
  have htop : S = ⊤ := by
    let S' : Subrepresentation π.ρ := ⟨S, fun x v hv => hSst x v hv⟩
    rcases π.irr.eq_bot_or_eq_top S' with h | h
    · exact absurd (congrArg Subrepresentation.toSubmodule h) hS0
    · exact congrArg Subrepresentation.toSubmodule h
  rw [htop, top_le_iff] at hST
  show Subsingleton (_ ⧸ twKer π.ρ (unipRad k e) 1)
  rw [Submodule.Quotient.subsingleton_iff]
  exact hST

end PositivityTheory.Rg.DzCount

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsUnitRho
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

namespace DepthZeroEigenvalues

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_good {y : WD h} (hi : IsIrrWD y) (ht : IsTameWD y) :
    ∃ (m : ℕ) (a : WDRep h (Fin m → ℂ)), WD.mk a = y ∧ a.ρ.IsIrreducible ∧
      ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1 := by
  obtain ⟨m, a, rfl, ha⟩ := hi
  obtain ⟨m', b, hb, hbt⟩ := ht
  have hba : b.Iso a := WD.mk_eq_mk.mp hb
  exact ⟨m, a, rfl, ha, fun σ hσ => hba.ρ_eq_one (hbt σ hσ)⟩

theorem isUnit_rho {m : ℕ} (a : WDRep h (Fin m → ℂ)) (σ : Weil h) : IsUnit (a.ρ σ) :=
  (Group.isUnit σ).map a.ρ

theorem eig_prod {m : ℕ} (a : WDRep h (Fin m → ℂ)) (σ : Weil h) :
    ((WD.mk a).eig σ).prod = LinearMap.det (a.ρ σ) := by
  rw [WD.eig_mk, Module.End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _)]

theorem card_res (w : HeightOneSpectrum (𝓞 E)) : Nat.card 𝓀[w.adicCompletion E] = normV w :=
  resCard_eq_normV w

end DepthZeroEigenvalues

open DepthZeroEigenvalues in
theorem st3 : St1a → St1b → St2 → St3a → St3 := by
  intro h1a h1b h2 h3a E Ω _ _ _ _ _ A w h φ hφ n c hn
  obtain ⟨γ, hγ1, hγ2⟩ := h2 E Ω A w h φ hφ
  have hq : Nat.card 𝓀[w.adicCompletion E] = normV w := card_res w
  have : Finite 𝓀[w.adicCompletion E] := inferInstance
  obtain ⟨lab, hlab1, hlab2⟩ := h3a 𝓀[w.adicCompletion E] n hn
  set q := Nat.card 𝓀[w.adicCompletion E] with hqdef

  let Pz : WD h → ℂ → Prop := fun y z => ∃ (m : ℕ) (a : WDRep h (Fin m → ℂ)), WD.mk a = y ∧
    a.ρ.IsIrreducible ∧ (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1) ∧
    Module.End.HasEigenvalue (a.ρ γ) z ∧ ExactPer q n z
  have hex : ∀ y ∈ TameSet φ n c, ∃ z, Pz y z := by
    intro y hy
    obtain ⟨m, a, rfl, hai, hat⟩ := exists_good hy.1 hy.2.1
    have hm : Module.finrank ℂ (Fin m → ℂ) = n := by
      have := hy.2.2.1
      rwa [WD.lpDim_mk] at this
    obtain ⟨hc, hirr⟩ := hγ1 m a hat
    obtain ⟨z, hz1, hz2⟩ := h1a (Fin m → ℂ) (normV w) (a.ρ γ) (a.ρ φ) (isUnit_rho a γ)
      (isUnit_rho a φ) hc (hirr hai)
    refine ⟨z, m, a, rfl, hai, hat, hz1, ?_⟩
    rw [hm] at hz2
    rw [hq]; exact hz2
  let zf : WD h → ℂ := fun y => Classical.epsilon (Pz y)
  have hzf : ∀ y ∈ TameSet φ n c, Pz y (zf y) := fun y hy => Classical.epsilon_spec (hex y hy)
  refine ⟨fun y => lab (zf y), ?_, ?_⟩
  · intro y hy
    obtain ⟨_, _, _, _, _, _, hz⟩ := hzf y hy
    exact hlab1 _ hz
  · intro y hy y' hy' heq
    obtain ⟨m, a, rfl, hai, hat, hz1, hz2⟩ := hzf y hy
    obtain ⟨m', a', rfl, hai', hat', hz1', hz2'⟩ := hzf y' hy'
    obtain ⟨i, hi⟩ := hlab2 _ _ hz2 hz2' heq
    have hm : Module.finrank ℂ (Fin m → ℂ) = n := by
      have := hy.2.2.1
      rwa [WD.lpDim_mk] at this
    have hm' : Module.finrank ℂ (Fin m' → ℂ) = n := by
      have := hy'.2.2.1
      rwa [WD.lpDim_mk] at this
    have hdet : LinearMap.det (a.ρ φ) = LinearMap.det (a'.ρ φ) := by
      rw [← eig_prod, ← eig_prod, hy.2.2.2, hy'.2.2.2]
    obtain ⟨hc, -⟩ := hγ1 m a hat
    obtain ⟨hc', -⟩ := hγ1 m' a' hat'
    rw [← hq] at hc hc'
    obtain ⟨e, he1, he2⟩ := h1b (Fin m → ℂ) (Fin m' → ℂ) q n i (a.ρ γ) (a.ρ φ) (a'.ρ γ) (a'.ρ φ)
      (zf (WD.mk a)) hn hm hm' (isUnit_rho a φ) (isUnit_rho a' φ) hc hc' hz2 hz1 (hi ▸ hz1') hdet
    exact WD.mk_eq_mk.mpr (hγ2 m m' a a' hat hat' hai hai' e he1 he2)

end PositivityTheory.Rg.DzCount
end
end

