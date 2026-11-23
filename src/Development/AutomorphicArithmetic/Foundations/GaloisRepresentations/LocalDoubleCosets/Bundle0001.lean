module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
public import GroundTheory.AutomorphicForms.GeometricLemmaFiltration
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0065

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.CellStep
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD
open GroundTheory.Automorphic.Whittaker

theorem UpperTheory.Gal.LocD.cellStep :
    StabSub → CellStep := by
  intro hSt X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hsτ χ hχL D hD hsum U C x₀ hU hC hUC hHU hsU hsx₀ hvan f hf
  obtain ⟨L, hLo, hL1⟩ := hχL
  obtain ⟨L₀, hL₀c, hL₀o, hL₀L, hL₀τ⟩ := hSt H τ p hp hτ hτp L hLo
  have hχL₀ : ∀ l ∈ L₀, χ l = 1 := fun l hl => hL1 l (hL₀L hl)
  have hsp' : ∀ y, s^[p - 1 + 1] y = y := fun y => by rw [Nat.sub_add_cancel hp]; exact hsp y
  have toCc : ∀ g ∈ supportedIn U, g ∈ Cc X := by
    intro g hg
    obtain ⟨h1, -⟩ := hg
    exact h1
  let e : X ≃ₜ X :=
    { toFun := s
      invFun := s^[p - 1]
      left_inv := fun y => by
        show s^[p - 1] (s y) = y
        rw [← Function.iterate_succ_apply s (p - 1) y]
        exact hsp' y
      right_inv := fun y => by
        show s (s^[p - 1] y) = y
        rw [← Function.iterate_succ_apply' s (p - 1) y]
        exact hsp' y
      continuous_toFun := hs
      continuous_invFun := hs.iterate (p - 1) }
  have hcomp : ∀ g ∈ supportedIn U, g ∘ s ∈ supportedIn U := by
    intro g hg
    obtain ⟨hg1, hsupp⟩ := hg
    rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hg1
    obtain ⟨hlc, hcs⟩ := hg1
    refine ⟨GroundTheory.Automorphic.mem_locallyConstantCompactSupport.2
      ⟨hlc.comp_continuous hs, hcs.comp_homeomorph e⟩, ?_⟩
    intro x hx
    exact (hsU x).1 (hsupp hx)
  have hiter : ∀ i, ∀ g ∈ supportedIn U, g ∘ s^[i] ∈ supportedIn U := by
    intro i
    induction i with
    | zero =>
      intro g hg
      exact hg
    | succ i ih =>
      intro g hg
      exact hcomp _ (ih g hg)
  obtain ⟨f₀, hf₀U, hf₀eq⟩ :=
    exists_lift_orbit_piece hU hC hUC hL₀c hL₀o (y := x₀) (mem_orbit_self x₀)
  have hs_orb : ∀ y ∈ orbit H x₀, s y ∈ orbit H x₀ := by
    rintro _ ⟨h, rfl⟩
    exact ⟨τ h, by
      show τ h • x₀ = s (h • x₀)
      rw [hsτ, hsx₀]⟩
  have hs_piece : ∀ z ∈ orbitPiece L₀ x₀, s z ∈ orbitPiece L₀ x₀ := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨τ l, (hL₀τ l).2 hl, by
      show τ l • x₀ = s (l • x₀)
      rw [hsτ, hsx₀]⟩
  have hpiece_iter : ∀ n, ∀ z ∈ orbitPiece L₀ x₀, s^[n] z ∈ orbitPiece L₀ x₀ := by
    intro n
    induction n with
    | zero =>
      intro z hz
      exact hz
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply']
      exact hs_piece _ (ih z hz)
  have hs_piece_iff : ∀ z, s z ∈ orbitPiece L₀ x₀ ↔ z ∈ orbitPiece L₀ x₀ := by
    intro z
    refine ⟨fun hz => ?_, hs_piece z⟩
    have h1 := hpiece_iter (p - 1) _ hz
    rw [← Function.iterate_succ_apply s (p - 1) z, hsp'] at h1
    exact h1
  have hf₀s : ∀ x ∈ orbit H x₀, f₀ (s x) = f₀ x := by
    intro x hx
    rw [hf₀eq _ (hs_orb x hx), hf₀eq x hx]
    by_cases hz : x ∈ orbitPiece L₀ x₀
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hs_piece_iff x).2 hz)]
      rfl
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz ((hs_piece_iff x).1 h))]
  have hf₀i : ∀ i, ∀ x ∈ orbit H x₀, f₀ (s^[i] x) = f₀ x := by
    intro i
    induction i with
    | zero =>
      intro x _
      rfl
    | succ i ih =>
      intro x hx
      rw [Function.iterate_succ_apply, ih _ (hs_orb x hx)]
      exact hf₀s x hx
  have hDi : ∀ i, D (f₀ ∘ s^[i]) = D f₀ := by
    intro i
    have hm := sub_mem_of_eqOn_orbit hUC (hiter i f₀ hf₀U) hf₀U (fun x hx => hf₀i i x hx)
    have h0 := hvan _ hm
    rwa [map_sub, sub_eq_zero] at h0
  have hD0 : D f₀ = 0 := by
    have h0 := hsum f₀ (toCc f₀ hf₀U)
    simp only [hDi, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr hp.ne')
    · exact h
  let W : Submodule ℂ (X → ℂ) := supportedIn U ⊓ LinearMap.ker D
  have hrel : relSpan χ U ≤ W := by
    refine le_inf (relSpan_le_supportedIn χ hHU) (Submodule.span_le.mpr ?_)
    rintro g ⟨h, f', hf'U, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul]
    rw [hD h f' (toCc f' hf'U)]
    ring
  have hmem : f₀ ∈ W ⊔ supportedIn U ⊓ vanishingOn C :=
    Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hf₀U, LinearMap.mem_ker.mpr hD0⟩)
  have hle := supportedIn_le_of_base hU hC hUC hHU χ (W := W) inf_le_left hrel L₀ hL₀c hL₀o
    hχL₀ f₀ hf₀eq hmem
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hle hf)
  rw [map_add (f := _), LinearMap.mem_ker.mp (Submodule.mem_inf.mp ha).2, hvan b hb, add_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.DistInv
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

private theorem comp_mem_Cc {X : Type} [TopologicalSpace X] (s : X → X) (q : ℕ) (hs : Continuous s)
    (hsp : ∀ x, s^[q + 1] x = x) {f : X → ℂ} (hf : f ∈ Cc X) : f ∘ s ∈ Cc X := by
  obtain ⟨h1, h2⟩ := hf
  let e : X ≃ₜ X :=
    { toFun := s
      invFun := s^[q]
      left_inv := fun y => by
        show s^[q] (s y) = y
        rw [← Function.iterate_succ_apply s q y, hsp]
      right_inv := fun y => by
        show s (s^[q] y) = y
        rw [← Function.iterate_succ_apply' s q y, hsp]
      continuous_toFun := hs
      continuous_invFun := hs.iterate q }
  exact ⟨h1.comp_continuous hs, h2.comp_homeomorph e⟩

theorem UpperTheory.Gal.LocD.distInv :
    DistZero → DistInv := by
  intro hZ X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hsτ χ hχL hχτ k x hxs horb hcl D hD f hf
  have hsp' : ∀ y, s^[p - 1 + 1] y = y := fun y => by rw [Nat.sub_add_cancel hp]; exact hsp y
  have cc : ∀ g ∈ Cc X, g ∘ s ∈ Cc X := fun g hg => comp_mem_Cc s (p - 1) hs hsp' hg
  let D' : (X → ℂ) →ₗ[ℂ] ℂ := D.comp (LinearMap.funLeft ℂ ℂ s) - D
  have hD'apply : ∀ g, D' g = D (g ∘ s) - D g := fun g => rfl
  have key := hZ X H s τ p hp hs hτ hsp hτp hsτ χ hχL k x hxs horb hcl D' ?_ ?_ f hf
  · rw [hD'apply, sub_eq_zero] at key
    exact key
  · intro h g hg
    rw [hD'apply, hD'apply]
    set h' := τ^[p - 1] h with hh'
    have hτh : τ h' = h := by
      rw [hh', ← Function.iterate_succ_apply' τ (p - 1) h, Nat.succ_eq_add_one,
        Nat.sub_add_cancel hp, hτp]
    have hχh : χ h' = χ h := by rw [← hχτ h', hτh]
    have hcomp : GroundTheory.Automorphic.Whittaker.transl h g ∘ s
        = GroundTheory.Automorphic.Whittaker.transl h' (g ∘ s) := by
      ext y
      simp only [Function.comp_apply, GroundTheory.Automorphic.Whittaker.transl_apply]
      rw [hsτ, map_inv, hτh]
    rw [hcomp, hD h' _ (cc g hg), hD h g hg, hχh]
    ring
  · intro g hg
    have h1 : ∀ i, D' (g ∘ s^[i]) = D (g ∘ s^[i + 1]) - D (g ∘ s^[i]) := fun i => rfl
    simp only [h1]
    rw [Finset.sum_range_sub (fun i => D (g ∘ s^[i]))]
    have hid : s^[p] = id := funext hsp
    simp [hid]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.DistZero
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.distZero :
    CellStep → DistZero := by
  intro hstep X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hcomm χ hχ k x hfix huniq hcl D hD hsum f hf
  obtain ⟨C, hC⟩ : ∃ C : Fin k → Set X, C = fun j => MulAction.orbit H (x j) := ⟨_, rfl⟩
  have hCl : ∀ l y, y ∈ C l ↔ y ∈ MulAction.orbit H (x l) := by
    intro l y
    rw [hC]
  have hcov : ∀ y, ∃ l, y ∈ C l := fun y => ⟨(huniq y).exists.choose, (hCl _ _).mpr (huniq y).exists.choose_spec⟩
  have hdisj : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro y hi hj
    exact hij ((huniq y).unique ((hCl _ _).mp hi) ((hCl _ _).mp hj))
  have hcl' : ∀ j, closure (C j) ⊆ ⋃ l, ⋃ (_ : j ≤ l), C l := by
    rw [hC]
    exact hcl
  have hsorb : ∀ l y, y ∈ C l → s y ∈ C l := by
    intro l y hy
    rw [hCl] at hy ⊢
    obtain ⟨g, rfl⟩ := hy
    exact ⟨τ g, by rw [hcomm, hfix]⟩
  have key : ∀ j : ℕ, j ≤ k → ∀ g ∈ GroundTheory.Automorphic.Whittaker.supportedIn (GroundTheory.Automorphic.Parabolic.cellUnion C j), D g = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ g hg
      rw [GroundTheory.Automorphic.Whittaker.mem_supportedIn, GroundTheory.Automorphic.Parabolic.cellUnion_zero] at hg
      have hg0 : g = 0 := by
        funext y
        by_contra hy
        exact hg.2 hy
      rw [hg0, map_zero]
    | succ j ih =>
      intro hjk g hg
      have hj : j < k := by omega
      have hU : GroundTheory.Automorphic.Parabolic.cellUnion C (j + 1) = GroundTheory.Automorphic.Parabolic.cellUnion C ((⟨j, hj⟩ : Fin k) : ℕ) ∪ C ⟨j, hj⟩ :=
        GroundTheory.Automorphic.Parabolic.cellUnion_succ (C := C) ⟨j, hj⟩
      refine hstep X H s τ p hp hs hτ hsp hτp hcomm χ hχ D hD hsum
        (GroundTheory.Automorphic.Parabolic.cellUnion C (j + 1)) (closure (C ⟨j, hj⟩)) (x ⟨j, hj⟩)
        (GroundTheory.Automorphic.Parabolic.isOpen_cellUnion hdisj hcov hcl' (j + 1)) isClosed_closure ?_ ?_ ?_ (hfix _) ?_ g hg
      · rw [Set.inter_comm]
        have h1 := GroundTheory.Automorphic.Parabolic.closure_inter_cellUnion_succ hdisj hcl' ⟨j, hj⟩
        rw [h1, hC]
      · intro h y hy
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion] at hy ⊢
        obtain ⟨l, hl, hyl⟩ := hy
        refine ⟨l, hl, ?_⟩
        rw [hCl] at hyl ⊢
        obtain ⟨g', rfl⟩ := hyl
        exact ⟨h * g', mul_smul _ _ _⟩
      · intro y
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion, GroundTheory.Automorphic.Parabolic.mem_cellUnion]
        constructor
        · rintro ⟨l, hl, hsy⟩
          obtain ⟨m, hm⟩ := hcov y
          have hlm : l = m := (huniq (s y)).unique ((hCl _ _).mp hsy) ((hCl _ _).mp (hsorb m y hm))
          subst hlm
          exact ⟨l, hl, hm⟩
        · rintro ⟨l, hl, hy⟩
          exact ⟨l, hl, hsorb l y hy⟩
      · intro g' hg'
        rw [Submodule.mem_inf, GroundTheory.Automorphic.Whittaker.mem_supportedIn, GroundTheory.Automorphic.Whittaker.mem_vanishingOn] at hg'
        obtain ⟨hg1, hg2⟩ := hg'
        apply ih (by omega)
        rw [GroundTheory.Automorphic.Whittaker.mem_supportedIn]
        refine ⟨hg1.1, ?_⟩
        intro y hy
        have hyU := hg1.2 hy
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion] at hyU ⊢
        obtain ⟨l, hl, hyl⟩ := hyU
        refine ⟨l, ?_, hyl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq
        · exact hlt
        · exfalso
          apply hy
          apply hg2
          have hleq : l = ⟨j, hj⟩ := Fin.ext heq
          rw [hleq] at hyl
          exact subset_closure hyl
  apply key k le_rfl f
  rw [GroundTheory.Automorphic.Parabolic.cellUnion_of_cover hcov, GroundTheory.Automorphic.Whittaker.mem_supportedIn]
  exact ⟨hf, Set.subset_univ _⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.EigZero
section
noncomputable section

namespace UpperTheory.Gal.LocD

private theorem common_eigenvector {T D : Type} [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D] [Nontrivial D]
    (φ : T → Module.End ℂ D) (hc : ∀ s t, Commute (φ s) (φ t)) :
    ∃ (l : D) (a : T → ℂ), l ≠ 0 ∧ ∀ t, φ t l = a t • l :=
  _root_.UpperTheory.Reformulated.B.CommonEigenvectorExistence.common_eigenvector φ hc

theorem eigZero : EigZero := by
  intro T J _ _ _ _ _ ρ
  have hcomm : ∀ s t, Commute (ρ s) (ρ t) := fun s t => by
    change ρ s * ρ t = ρ t * ρ s
    rw [← map_mul, ← map_mul, mul_comm]
  haveI : Nontrivial (Module.Dual ℂ J) := by
    obtain ⟨y, hy⟩ := exists_ne (0 : J)
    have hex : ∃ g : Module.Dual ℂ J, g y ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 h)
    obtain ⟨g, hg⟩ := hex
    exact ⟨g, 0, fun h => hg (by simp [h])⟩
  obtain ⟨l, a, hl0, hl⟩ := common_eigenvector (fun t => (ρ t).dualMap) (fun s t => by
    change (ρ s).dualMap * (ρ t).dualMap = (ρ t).dualMap * (ρ s).dualMap
    ext g y
    have h := congrArg (fun F : Module.End ℂ J => F y) (hcomm s t).eq
    simp only [Module.End.mul_apply] at h
    simp [Module.End.mul_apply, LinearMap.dualMap_apply, h])
  have hact : ∀ t y, l (ρ t y) = a t * l y := fun t y => by
    have := congrArg (fun g : Module.Dual ℂ J => g y) (hl t)
    simpa [LinearMap.dualMap_apply] using this
  obtain ⟨y₀, hy₀⟩ : ∃ y, l y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hl0 (LinearMap.ext h)
  let am : T →* ℂ :=
    { toFun := a
      map_one' := by
        have := hact 1 y₀
        simp only [map_one, Module.End.one_apply] at this
        exact (mul_right_cancel₀ hy₀ (by rw [one_mul]; exact this)).symm
      map_mul' := fun s t => by
        have := hact (s * t) y₀
        rw [map_mul, Module.End.mul_apply, hact s, hact t, ← mul_assoc] at this
        exact (mul_right_cancel₀ hy₀ this).symm }
  refine ⟨am.toHomUnits, l, ?_, ?_, ?_⟩
  · exact hl0
  · intro t y
    simpa [am] using hact t y
  · have hval : ∀ t, ((am.toHomUnits t : ℂˣ) : ℂ) = a t := fun t => by simp [am]
    have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (fun t => ρ t) (fun s t _ => hcomm s t)
      (fun t => Module.End.iSup_maxGenEigenspace_eq_top (ρ t))
    obtain ⟨χ, y, hy, hly⟩ : ∃ (χ : T → ℂ) (y : J),
        y ∈ (⨅ t, Module.End.maxGenEigenspace (ρ t) (χ t) : Submodule ℂ J) ∧ l y ≠ 0 := by
      by_contra h
      push_neg at h
      have : (⊤ : Submodule ℂ J) ≤ LinearMap.ker l := by
        rw [← htop]
        exact iSup_le fun χ y hy => LinearMap.mem_ker.2 (h χ y hy)
      exact hl0 (LinearMap.ker_eq_top.1 (top_le_iff.1 this))
    have hpow : ∀ (t : T) (c : ℂ) (m : ℕ) (z : J), l (((ρ t - c • 1) ^ m) z) = (a t - c) ^ m * l z := by
      intro t c m
      induction m with
      | zero => intro z; simp
      | succ m ih =>
        intro z
        rw [pow_succ, Module.End.mul_apply, ih]
        simp [hact, pow_succ, sub_mul, mul_assoc]
    have hχ : ∀ t, χ t = a t := by
      intro t
      obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hy t)
      have h0 := hpow t (χ t) m y
      rw [hm, map_zero] at h0
      have : (a t - χ t) ^ m = 0 := by
        rcases mul_eq_zero.1 h0.symm with h | h
        · exact h
        · exact absurd h hly
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at this
      exact (sub_eq_zero.1 ((pow_eq_zero_iff hm0).1 this)).symm
    intro hbot
    have hy' : y ∈ (⨅ t, Module.End.maxGenEigenspace (ρ t) ((am.toHomUnits t : ℂˣ) : ℂ) : Submodule ℂ J) := by
      simp only [hval, ← hχ]
      exact hy
    rw [hbot, Submodule.mem_bot] at hy'
    exact hly (by rw [hy', map_zero])

end UpperTheory.Gal.LocD

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.EtaEx
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.etaEx :
    EtaEx := by
  intro G _ _ _ _ _ _ B s p hp hper P κ hκ hs hB hne
  obtain ⟨f₀, hf₀, g₀, h0⟩ := hne
  obtain ⟨K, hK, hKf⟩ := GroundTheory.Automorphic.exists_forall_mul_left (R := ℂ) hf₀
  set e : B → ℂ := fun b => P (fun x => f₀ ((b : G)⁻¹ * x)) g₀ / P f₀ g₀ with he
  have hη : ∀ (b : B) (f : G → ℂ) (g : G), P (fun x => f ((b : G)⁻¹ * x)) g = e b * P f g := by
    intro b f g
    obtain ⟨c, hc⟩ := hB b
    have hc0 := hc f₀ g₀
    have : e b = c := by
      rw [he]; dsimp only; rw [hc0, mul_div_assoc, div_self h0, mul_one]
    rw [this, hc]
  have hpow : ∀ (n : ℕ) (f : G → ℂ) (g : G), P (f ∘ s^[n]) g = (κ : ℂ) ^ n * P f (s^[n] g) := by
    intro n
    induction n with
    | zero => intro f g; simp
    | succ n ih =>
      intro f g
      rw [Function.iterate_succ, ← Function.comp_assoc, hs, ih, Function.comp_apply, pow_succ]
      ring
  have hper' : s^[p] = id := funext hper
  have hκ1 : κ = 1 := by
    have h1 := hpow p f₀ g₀
    rw [hper', Function.comp_id, id] at h1
    have hk : (κ : ℂ) ^ p = 1 := by
      have := mul_right_cancel₀ h0 (h1.symm.trans (one_mul _).symm)
      exact this
    have hk' : κ ^ p = 1 := by exact_mod_cast hk
    exact (pow_eq_one_iff_of_nonneg hκ.le hp.ne').1 hk'
  have e1 : e 1 = 1 := by
    rw [he]; dsimp only; simp [div_self h0]
  have emul : ∀ b b' : B, e (b * b') = e b * e b' := by
    intro b b'
    have h := hη b (fun x => f₀ ((b' : G)⁻¹ * x)) g₀
    rw [hη b' f₀ g₀] at h
    have h2 : e (b * b') * P f₀ g₀ = e b * e b' * P f₀ g₀ := by
      rw [← hη, mul_assoc, ← h]
      congr 1
      funext x
      simp [mul_assoc]
    exact mul_right_cancel₀ h0 h2
  let η : B →* ℂ := { toFun := e, map_one' := e1, map_mul' := emul }
  refine ⟨hκ1, η, fun b f g => hη b f g, ⟨K, K.isOpen, fun b hb => ?_⟩, fun b b' hbb => ?_⟩
  · show e b = 1
    rw [he]
    dsimp only
    have hfix : (fun x => f₀ ((b : G)⁻¹ * x)) = f₀ :=
      funext fun x => hKf _ (K.inv_mem (by exact hb)) x
    rw [hfix, div_self h0]
  · show e b' = e b
    have hg1 : s (s^[p - 1] g₀) = g₀ := by
      rw [← Function.iterate_succ_apply' (f := s), Nat.succ_eq_add_one, Nat.sub_add_cancel hp,
        hper]
    have hA := hη b (f₀ ∘ s) (s^[p - 1] g₀)
    rw [hs, hg1] at hA
    have hfun : (fun x => (f₀ ∘ s) ((b : G)⁻¹ * x)) = (fun x => f₀ ((b' : G)⁻¹ * x)) ∘ s := by
      funext x
      simp [hbb, map_mul, map_inv]
    rw [hfun, hs, hg1, hη b' f₀ g₀] at hA
    have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have h3 : e b' * P f₀ g₀ = e b * P f₀ g₀ := by
      have := mul_left_cancel₀ hκ0 (hA.trans (by ring : e b * (↑κ * P f₀ g₀) = ↑κ * (e b * P f₀ g₀)))
      exact this
    exact mul_right_cancel₀ h0 h3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.Imports
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.eig :
    EigZero → Eig := by
  intro hE T J _ _ _ _ _ ρ s A hA hμs
  obtain ⟨μ, l0, hl0, hl0eq, hgen⟩ := hE T J ρ
  have hμ : ∀ t, μ (s t) = μ t := hμs μ hgen
  let W : Submodule ℂ (Module.Dual ℂ J) :=
    { carrier := {l | ∀ t y, l (ρ t y) = (μ t : ℂ) * l y}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        intro t y
        simp only [LinearMap.add_apply, ha t y, hb t y]
        ring
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        intro t y
        simp
      smul_mem' := by
        intro c l hl
        simp only [Set.mem_setOf_eq] at *
        intro t y
        simp only [LinearMap.smul_apply, smul_eq_mul, hl t y]
        ring }
  have hAW : ∀ l ∈ W, LinearMap.dualMap A l ∈ W := by
    intro l hl t y
    show l (A (ρ t y)) = (μ t : ℂ) * l (A y)
    rw [hA, hl, hμ]
  let A' : W →ₗ[ℂ] W := (LinearMap.dualMap A).restrict hAW
  haveI : Nontrivial W := ⟨⟨⟨l0, hl0eq⟩, 0, fun h => hl0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A'
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨μ, (v : Module.Dual ℂ J), c, fun h => hv.2 (Subtype.ext h), hμ, v.2, fun y => ?_⟩
  have := congrArg (fun w : W => (w : Module.Dual ℂ J) y) hv.apply_eq_smul
  simpa [A'] using this
end

