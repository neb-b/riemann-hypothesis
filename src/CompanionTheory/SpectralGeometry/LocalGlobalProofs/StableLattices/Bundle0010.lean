module

public import Mathlib
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsPiecesPiece
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0006
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0005
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0007
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0001

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriStatement
section
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

theorem isCongIdeal_congJ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] {Λ : AddSubgroup V} (hΛ : IsLat L Λ)
    {π : L} (hπ : ‖π‖ < 1) {ι : Type} (P : ι → Module.End L V)
    (hP : ∀ i, ∀ x ∈ Λ, P i x ∈ Λ) : IsCongIdeal (congJ Λ π) P := by
  refine ⟨?_, ?_, ?_, _root_.GlobalTheory.CompanionTheory.Iwahori.CongUnit.main Λ hΛ π hπ⟩
  · intro x hx y hy v hv
    obtain ⟨z, hz, e1⟩ := hy v hv
    obtain ⟨w, hw, e2⟩ := hx z hz
    refine ⟨π • w, lat_smul hΛ hπ.le hw, ?_⟩
    simp [Module.End.mul_apply, e1, e2]
  · intro i x hx v hv
    obtain ⟨z, hz, e1⟩ := hx v hv
    exact ⟨P i z, hP i z hz, by simp [Module.End.mul_apply, e1]⟩
  · intro i x hx v hv
    exact hx _ (hP i v hv)

theorem congJ_smul {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
    {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (π : L) (c : L) (hc : ‖c‖ ≤ 1) (x : Module.End L V)
    (hx : x ∈ congJ Λ π) : c • x ∈ congJ Λ π := by
  intro v hv
  obtain ⟨z, hz, e1⟩ := hx v hv
  refine ⟨c • z, lat_smul hΛ hc hz, ?_⟩
  simp [e1, smul_comm c π z]

theorem isUpper_rev_iff {E : Type} [Ring E] {l : ℕ} (P : Idx l → E) (b : E) :
    IsUpper (fun i => 2 * l - wt i) P b ↔ IsLower wt P b := by
  constructor
  · intro H i j hij
    exact H i j (by have := wt_le i; have := wt_le j; simp only; omega)
  · intro H i j hij
    refine H i j ?_
    have := wt_le i; have := wt_le j
    simp only at hij
    omega

theorem stIwahori : StIwahori := by
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh l e f W Λ hF hΛ hA π hπ k hk hc
  have hδ0 : δ ≠ 0 := hδ.1
  set P := piece hh δ e f with hPdef
  have hP : IsPieces P := isPieces_piece hh hδ0 hF
  have hJ : IsCongIdeal (congJ Λ π) P :=
    isCongIdeal_congJ hΛ hπ P fun i x hx => piece_mem hΛ hA hh hδ0 hF i hx
  obtain ⟨st, hst, st_mul, st_one, st_zero, st_P⟩ :=
    exists_star (δ := δ) (e := e) (f := f) (l := l) hs hh (_root_.GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm s hs h hh)
  have hk1 : (k.toLinearMap : Module.End L V) - 1 ∈ congJ Λ π := fun x hx => by
    obtain ⟨y, hy, e1⟩ := hc x hx
    exact ⟨y, hy, by simpa using e1⟩
  obtain ⟨a, b, ha, hb, hup, hlo, hab⟩ := _root_.GlobalTheory.CompanionTheory.Iwahori.Gauss.block_gauss wt wt_injective P hP _ hJ _ hk1

  obtain ⟨ya, hya, ia1, ia2⟩ := hJ.inv _ ha
  obtain ⟨yb, hyb, ib1, ib2⟩ := hJ.inv _ hb
  rw [add_sub_cancel] at ia1 ia2 ib1 ib2
  have hkk : ∀ y, st (k.toLinearMap) (k y) = y := fun y => by
    refine eq_of_pair hh fun x => ?_
    have := hst k.toLinearMap x (k y)
    simp only [LinearEquiv.coe_coe] at this
    rw [← this, hk x y]
  have hk2 : st (k.toLinearMap) * (k.toLinearMap) = 1 := by
    ext y; exact hkk y
  have hk3 : (k.toLinearMap : Module.End L V) * st (k.toLinearMap) = 1 := by
    ext y
    obtain ⟨z, rfl⟩ := k.surjective y
    simp [Module.End.mul_apply, hkk z]
  rw [hab] at hk2 hk3
  obtain ⟨ua, ub⟩ := _root_.GlobalTheory.CompanionTheory.Iwahori.Unitary.st_mul_self_of_factor wt P hP rev rev_rev
    (fun i j hij => by have := wt_rev i; have := wt_rev j; omega) wt_injective st st_mul st_one st_zero st_P
    (fun a a' h1 h2 h3 => _root_.GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv wt P hP a a' h1 h2 h3)
    (fun a a' h1 h2 h3 => (isUpper_rev_iff P a').1 (_root_.GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv _ P hP a a' h1 h2 ((isUpper_rev_iff P a).2 h3)))
    a (1 + ya) b (1 + yb) ia1 ia2 ib1 ib2 hup hlo hk2 hk3
  let A : V ≃ₗ[L] V := LinearEquiv.ofLinear a (1 + ya) ia1 ia2
  let B : V ≃ₗ[L] V := LinearEquiv.ofLinear b (1 + yb) ib1 ib2
  have isoOf : ∀ (g : V ≃ₗ[L] V), st (g.toLinearMap) * g.toLinearMap = 1 → IsIso h g := fun g hg x y => by
    have := hst g.toLinearMap x (g y)
    simp only [LinearEquiv.coe_coe] at this
    rw [this]
    have h2 : st g.toLinearMap (g y) = y := by
      have := congrArg (fun m : Module.End L V => m y) hg
      simpa [Module.End.mul_apply] using this
    rw [h2]
  refine ⟨A, B, isoOf A ua, isoOf B ub, ?_, ?_⟩
  · ext x
    have := congrArg (fun m : Module.End L V => m x) hab
    simpa [A, B, Module.End.mul_apply] using this
  · intro u t hu0 hm h1 ht
    have hT := fun i => tor_piece (δ := δ) hh hδ0 hF ht i
    have key := GlobalTheory.T.torus_conjugation_preserves_congruence wt P hP _ hJ (congJ_smul hΛ π) (t.toLinearMap) (t.symm.toLinearMap) (tau s u)
      (tau_ne hu0) (by ext y; simp [Module.End.mul_apply]) (by ext y; simp [Module.End.mul_apply])
      (fun i => (hT i).1) (fun i => (hT i).2)
      (tau_mono hs hu0 hm h1) a b ha hb hup hlo.1
    constructor
    · intro x hx
      obtain ⟨y, hy, e1⟩ := key.1 x hx
      exact ⟨y, hy, by simpa [A, Module.End.mul_apply] using e1⟩
    · intro x hx
      obtain ⟨y, hy, e1⟩ := key.2 x hx
      exact ⟨y, hy, by simpa [B, Module.End.mul_apply] using e1⟩

end GlobalTheory.CompanionTheory.Iwahori

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ProjectionStatement
section
open scoped InnerProductSpace
open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted

namespace GlobalTheory.CompanionTheory.FixedProj

theorem stProj : StProj := by
  unfold StProj
  intro G H _ _ _ _ σ hiso K
  let V : Submodule ℂ H :=
    { carrier := {v | ∀ k ∈ K, σ k v = v}
      add_mem' := fun {a b} ha hb k hk => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_add (f := _), ha k hk, hb k hk]
      zero_mem' := fun k _ => map_zero _
      smul_mem' := fun c v hv k hk => by
        simp only [Set.mem_ofPred_eq] at hv ⊢
        rw [map_smul, hv k hk] }
  have hmem : ∀ v, v ∈ V ↔ ∀ k ∈ K, σ k v = v := fun v => Iff.rfl
  have hVc : IsClosed (V : Set H) := by
    have hV : (V : Set H) = ⋂ k ∈ K, {v | σ k v = v} := by
      ext v
      simp only [Set.mem_iInter]
      exact hmem v
    rw [hV]
    exact isClosed_biInter fun k _ => isClosed_eq (σ k).continuous continuous_id
  haveI : CompleteSpace V := hVc.completeSpace_coe
  have hin : ∀ g v w, inner ℂ (σ g v) w = inner ℂ v (σ g⁻¹ w) := CompanionTheory.D.gk.admitted.FinOfPIAux.inner_left σ hiso
  refine ⟨V.starProjection, ?_, ?_, ?_⟩
  · unfold IsAvg
    refine ⟨?_, ?_, ?_⟩
    · intro v k hk
      exact (hmem _).1 (V.starProjection_apply_mem v) k hk
    · intro v hv
      exact Submodule.starProjection_eq_self_iff.2 ((hmem v).2 hv)
    · intro v k hk
      have horth : σ k v - v ∈ Vᗮ := by
        rw [Submodule.mem_orthogonal]
        intro u hu
        have h1 : inner ℂ u (σ k v) = inner ℂ u v := by
          have h := hin k⁻¹ u v
          rw [inv_inv, (hmem u).1 hu k⁻¹ (K.inv_mem hk)] at h
          exact h.symm
        rw [inner_sub_right, h1, sub_self]
      have h0 := (Submodule.starProjection_apply_eq_zero_iff V).2 horth
      rw [map_sub, sub_eq_zero] at h0
      exact h0
  · intro u w
    exact Submodule.inner_starProjection_left_eq_right (K := V) u w
  · intro T hT
    have hTσ : ∀ g v, T (σ g v) = σ g (T v) := fun g v =>
      congrArg (fun S : H →L[ℂ] H => S v) (hT g)
    have hTV : ∀ v ∈ V, T v ∈ V := fun v hv k hk => by
      rw [← hTσ, (hmem v).1 hv k hk]
    have hadj : ∀ w ∈ V, ContinuousLinearMap.adjoint T w ∈ V := by
      intro w hw k hk
      apply ext_inner_right ℂ
      intro z
      rw [hin, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hTσ, ← hin,
        (hmem w).1 hw k hk]
    ext v
    have h1 : V.starProjection (T (V.starProjection v)) = T (V.starProjection v) :=
      Submodule.starProjection_eq_self_iff.2 (hTV _ (V.starProjection_apply_mem v))
    have hu : v - V.starProjection v ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal (K := V) v
    have h2 : V.starProjection (T (v - V.starProjection v)) = 0 := by
      apply (Submodule.starProjection_apply_eq_zero_iff V).2
      rw [Submodule.mem_orthogonal] at hu ⊢
      intro w hw
      rw [← ContinuousLinearMap.adjoint_inner_left]
      exact hu _ (hadj w hw)
    have hv : v = V.starProjection v + (v - V.starProjection v) := by abel
    show T (V.starProjection v) = V.starProjection (T v)
    conv_rhs => rw [hv]
    simp only [map_add (f := _)]
    rw [h1, h2, add_zero]

end GlobalTheory.CompanionTheory.FixedProj
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SimpleOfCommutativeStatement
section
noncomputable section

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

theorem finrank_sq_le_of_span {A V : Type} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (hρ : Function.Surjective ρ) {d l : ℕ}
    (x y : Fin d → A) (a : Fin l → A)
    (hs : Submodule.span ℂ {z | ∃ i j, ∃ c ∈ Algebra.adjoin ℂ (Set.range a), z = x i * c * y j} = ⊤) :
    Module.finrank ℂ V ^ 2 ≤
      d ^ 2 * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i => ρ (a i))) := by
  classical
  set B := Algebra.adjoin ℂ (Set.range fun i => ρ (a i)) with hB
  have hmap : ∀ c ∈ Algebra.adjoin ℂ (Set.range a), ρ c ∈ B := by
    intro c hc
    have e : B = (Algebra.adjoin ℂ (Set.range a)).map ρ := by
      rw [hB, AlgHom.map_adjoin, ← Set.range_comp]
      rfl
    rw [e]
    exact ⟨c, hc, rfl⟩
  let G : Fin d × Fin d → (B →ₗ[ℂ] Module.End ℂ V) := fun p =>
    (LinearMap.mulLeft ℂ (ρ (x p.1))) ∘ₗ (LinearMap.mulRight ℂ (ρ (y p.2))) ∘ₗ B.val.toLinearMap
  let F : (Fin d × Fin d → B) →ₗ[ℂ] Module.End ℂ V :=
    ∑ p : Fin d × Fin d, G p ∘ₗ LinearMap.proj p
  have hFs : ∀ (p : Fin d × Fin d) (b : B), F (Pi.single p b) = ρ (x p.1) * b * ρ (y p.2) := by
    intro p b
    simp only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single p]
    · simp [G, mul_assoc]
    · intro q _ hq
      simp [Pi.single_eq_of_ne hq]
    · simp
  have hF : LinearMap.range F = ⊤ := by
    rw [eq_top_iff]
    rintro f -
    obtain ⟨g, rfl⟩ := hρ f
    have hg : g ∈ Submodule.span ℂ {z | ∃ i j, ∃ c ∈ Algebra.adjoin ℂ (Set.range a), z = x i * c * y j} := by
      rw [hs]; exact Submodule.mem_top
    induction hg using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, j, c, hc, rfl⟩ := hz
      exact ⟨Pi.single (i, j) ⟨ρ c, hmap c hc⟩, by simp [hFs]⟩
    | zero => simp
    | add u v _ _ hu hv => simpa using Submodule.add_mem _ hu hv
    | smul t u _ hu => simpa using Submodule.smul_mem _ t hu
  have h1 : Module.finrank ℂ (Module.End ℂ V) ≤ Module.finrank ℂ (Fin d × Fin d → B) := by
    have := LinearMap.finrank_range_le F
    rwa [hF, finrank_top] at this
  have h2 : Module.finrank ℂ (Module.End ℂ V) = Module.finrank ℂ V ^ 2 := by
    rw [Module.finrank_linearMap, sq]
  have h3 : Module.finrank ℂ (Fin d × Fin d → B) = d ^ 2 * Module.finrank ℂ B := by
    rw [Module.finrank_pi_fintype]
    simp [sq]
  rw [h2, h3] at h1
  exact h1

theorem stSimple_of_stComm : StComm → StSimple := by
  intro h d l
  obtain ⟨C, hC⟩ := h l (2 * d ^ 2)
  refine ⟨C, fun A _ _ hA V _ _ _ ρ hirr => ?_⟩
  obtain ⟨x, y, a, hcomm, hs⟩ := hA
  rcases subsingleton_or_nontrivial V with hV | hV
  · simp [Module.finrank_zero_of_subsingleton]
  have hsurj := GlobalTheory.CompanionTheory.Burnside.burnside_surj_of_irred ρ hirr
  have h1 := finrank_sq_le_of_span ρ hsurj x y a hs
  have h2 := hC V (fun i => ρ (a i)) (fun i j => (hcomm i j).map ρ)
  have hm : 0 < Module.finrank ℂ V := Module.finrank_pos
  generalize Module.finrank ℂ V = m at *
  generalize Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i => ρ (a i))) = b at *
  have h3 : m * m ≤ C * m := by nlinarith
  exact Nat.le_of_mul_le_mul_right h3 hm

end GlobalTheory.CompanionTheory.RgFl

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StatementCommutative
section
open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.Bernstein

theorem arith_nil (N D D' E m K : ℕ) (hN : 0 < N)
    (h1 : D ≤ (2 * N - 1) * D' + E) (h2 : (2 * N - 1 + 1) * E ≤ m ^ 2)
    (h3 : 4 * N ^ 2 * D' ≤ m ^ 2 + K * m) : N * D ≤ m ^ 2 + K * m := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 2 * (k + 1) - 1 + 1 = 2 * (k + 1) := by omega
  rw [e1] at h1
  rw [e2] at h2
  have h4 : (2 * (k + 1)) * D ≤ (2 * (k + 1)) * ((2 * k + 1) * D') + m ^ 2 := by
    calc (2 * (k + 1)) * D ≤ (2 * (k + 1)) * ((2 * k + 1) * D' + E) :=
          Nat.mul_le_mul_left _ h1
      _ = (2 * (k + 1)) * ((2 * k + 1) * D') + (2 * (k + 1)) * E := by ring
      _ ≤ _ := Nat.add_le_add_left h2 _
  have h5 : (2 * (k + 1)) * ((2 * k + 1) * D') ≤ 4 * (k + 1) ^ 2 * D' := by
    have : (2 * (k + 1)) * ((2 * k + 1) * D') + 2 * (k + 1) * D' = 4 * (k + 1) ^ 2 * D' := by ring
    omega
  have h6 : (2 * (k + 1)) * D ≤ 2 * m ^ 2 + K * m := by omega
  have h7 : 2 * ((k + 1) * D) ≤ 2 * (m ^ 2 + K * m) := by
    have : (2 * (k + 1)) * D = 2 * ((k + 1) * D) := by ring
    have h8 : 2 * (m ^ 2 + K * m) = 2 * m ^ 2 + K * m + K * m := by ring
    omega
  omega

theorem adjoin_shift {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (μ : ℂ) :
    Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ) (fun i : Fin l => a i.succ) :
      Fin (l + 1) → Module.End ℂ V)) = Algebra.adjoin ℂ (Set.range a) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin ⟨0, rfl⟩) (Subalgebra.algebraMap_mem _ μ)
    · simp only [Fin.cons_succ]
      exact Algebra.subset_adjoin ⟨j.succ, rfl⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · have h0 : a 0 - algebraMap ℂ _ μ ∈ Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ)
          (fun i : Fin l => a i.succ) : Fin (l + 1) → Module.End ℂ V)) :=
        Algebra.subset_adjoin ⟨0, by simp⟩
      have := Subalgebra.add_mem _ h0 (Subalgebra.algebraMap_mem (Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ)
          (fun i : Fin l => a i.succ) : Fin (l + 1) → Module.End ℂ V))) μ)
      simpa using this
    · exact Algebra.subset_adjoin ⟨j.succ, by simp⟩

theorem positionOne_invariantIntegral_exchange_step (l N K : ℕ) (hN : 0 < N)
    (hK : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (a : Fin l → Module.End ℂ V), (∀ i j, Commute (a i) (a j)) →
      4 * N ^ 2 * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ V ^ 2 + K * Module.finrank ℂ V) :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (a : Fin (l + 1) → Module.End ℂ V), Module.finrank ℂ V = n → (∀ i j, Commute (a i) (a j)) →
      N * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ V ^ 2 + K * Module.finrank ℂ V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ a hn hc
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) = 0 :=
      Module.finrank_zero_of_subsingleton
    simp [this]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (a 0)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  set s : Module.End ℂ V := a 0 - algebraMap ℂ _ μ with hs
  have hsc : ∀ i, Commute s (a i) := fun i =>
    (hc 0 i).sub_left (Algebra.commutes μ (a i))
  have hsv : s v = 0 := by
    simp [hs, hv.apply_eq_smul, Module.algebraMap_end_apply]
  obtain ⟨k, hcompl, hk⟩ :=
    ((LinearMap.eventually_isCompl_ker_pow_range_pow s).and (Filter.eventually_ge_atTop 1)).exists
  have hkc : ∀ i, Commute (s ^ k) (a i) := fun i => (hsc i).pow_left k
  have h : ∀ i, ∀ w ∈ LinearMap.ker (s ^ k), a i w ∈ LinearMap.ker (s ^ k) := by
    intro i w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have := congrArg (fun f : Module.End ℂ V => f w) (hkc i).eq
    simp only [Module.End.mul_apply] at this
    rw [this, hw, map_zero]
  have h' : ∀ i, ∀ w ∈ LinearMap.range (s ^ k), a i w ∈ LinearMap.range (s ^ k) := by
    rintro i _ ⟨u, rfl⟩
    refine ⟨a i u, ?_⟩
    have := congrArg (fun f : Module.End ℂ V => f u) (hkc i).eq
    simpa only [Module.End.mul_apply] using this
  by_cases hr : LinearMap.range (s ^ k) = ⊥
  ·
    have hnil : IsNilpotent s := ⟨k, LinearMap.range_eq_bot.mp hr⟩
    set b : Fin (l + 1) → Module.End ℂ V := Fin.cons s (fun i : Fin l => a i.succ) with hb
    have hadj : Algebra.adjoin ℂ (Set.range b) = Algebra.adjoin ℂ (Set.range a) :=
      adjoin_shift a μ
    have hb0 : b 0 = s := rfl
    have hbs : ∀ i : Fin l, b i.succ = a i.succ := fun i => rfl
    have hbc : ∀ i j, Commute (b i) (b j) := by
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · exact Commute.refl _
      · rw [hb0, hbs]; exact hsc _
      · rw [hb0, hbs]; exact (hsc _).symm
      · rw [hbs, hbs]; exact hc _ _
    have hmem : ∀ c ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range b)), Commute c s := by
      intro c hcm
      have hle : Algebra.adjoin ℂ (Set.range b) ≤ Subalgebra.centralizer ℂ {s} := by
        apply Algebra.adjoin_le
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact hbc 0 i
      have := hle hcm
      rw [Subalgebra.mem_centralizer_iff] at this
      exact (this s rfl).symm
    have h1 := GlobalTheory.CompanionTheory.CommStep.comm_step V l b hbc (2 * N - 1)
    have h2 := GlobalTheory.CompanionTheory.CommNil.succ_mul_finrank_map_le V s hnil (2 * N - 1) _ hmem
    rw [hb0] at h1
    have h3 := hK V (fun i : Fin l => b i.succ) (fun i j => hbc _ _)
    rw [hadj] at h1 h2
    exact arith_nil N _ _ _ _ K hN h1 h2 h3
  ·
    have hker : LinearMap.ker (s ^ k) ≠ ⊥ := by
      intro hbot
      have hmem : v ∈ LinearMap.ker (s ^ k) := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hsv, map_zero]
      rw [hbot, Submodule.mem_bot] at hmem
      exact hv.2 hmem
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
    have p1 : Module.finrank ℂ (LinearMap.ker (s ^ k)) ≠ 0 := fun h0 =>
      hker (Submodule.finrank_eq_zero.mp h0)
    have p2 : Module.finrank ℂ (LinearMap.range (s ^ k)) ≠ 0 := fun h0 =>
      hr (Submodule.finrank_eq_zero.mp h0)
    have hres : ∀ (W : Submodule ℂ V) (g : ∀ i, ∀ w ∈ W, a i w ∈ W) (i j : Fin (l + 1)),
        Commute (((a i).restrict (g i) : Module.End ℂ W)) ((a j).restrict (g j)) := by
      intro W g i j
      show ((a i).restrict (g i) : Module.End ℂ W) * (a j).restrict (g j) =
        ((a j).restrict (g j) : Module.End ℂ W) * (a i).restrict (g i)
      refine LinearMap.ext fun w => Subtype.ext ?_
      have := congrArg (fun f : Module.End ℂ V => f w.1) (hc i j).eq
      simpa [Module.End.mul_apply] using this
    have i1 := ih (Module.finrank ℂ (LinearMap.ker (s ^ k))) (by omega) (LinearMap.ker (s ^ k))
      (fun i => ((a i).restrict (h i) : Module.End ℂ (LinearMap.ker (s ^ k)))) rfl (hres _ h)
    have i2 := ih (Module.finrank ℂ (LinearMap.range (s ^ k))) (by omega) (LinearMap.range (s ^ k))
      (fun i => ((a i).restrict (h' i) : Module.End ℂ (LinearMap.range (s ^ k)))) rfl (hres _ h')
    have h3 := GlobalTheory.CompanionTheory.CommSplit.finrank_adjoin_le_add V (l + 1) a _ _ hcompl h h'
    rw [← hsum]
    calc N * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a))
        ≤ N * (_ + _) := Nat.mul_le_mul_left _ h3
      _ = _ + _ := Nat.mul_add _ _ _
      _ ≤ _ := Nat.add_le_add i1 i2
      _ ≤ _ := by nlinarith [Nat.zero_le (Module.finrank ℂ (LinearMap.ker (s ^ k)) *
            Module.finrank ℂ (LinearMap.range (s ^ k)))]

theorem stComm : StComm := by
  unfold StComm
  intro l
  induction l with
  | zero =>
    intro N
    refine ⟨N, ?_⟩
    intro V _ _ _ a _
    have hr : Set.range a = ∅ := Set.range_eq_empty a
    rw [hr, Algebra.adjoin_empty]
    rcases subsingleton_or_nontrivial V with hV | hV
    · have : Module.finrank ℂ (⊥ : Subalgebra ℂ (Module.End ℂ V)) = 0 :=
        Module.finrank_zero_of_subsingleton
      simp [this]
    · have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
      rw [Subalgebra.finrank_bot]
      nlinarith
  | succ l ih =>
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨0, fun V _ _ _ a _ => by simp⟩
    obtain ⟨K, hK⟩ := ih (4 * N ^ 2)
    exact ⟨K, fun V _ _ _ a hc => positionOne_invariantIntegral_exchange_step l N K hN hK _ V a rfl hc⟩

end GlobalTheory.CompanionTheory.Bernstein
end

