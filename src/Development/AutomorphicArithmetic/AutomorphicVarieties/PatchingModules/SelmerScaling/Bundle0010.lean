module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUTest
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUPush
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefULift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlSel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.FirstOrderMatrixMemSquareZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EOneTranspose
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.ConjConst

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Claim2
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.claim2 :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ m : Fin S.k.g → S.U.N, S.DualM m → ∀ Φ ∈ S.Ph, ∃ α : Fin S.k.g → S.Tp, (∀ j b, (α j : S.Bh →+ S.F) b = Φ (b • m j) - S.rF b * Φ (m j)) ∧ Lifts S.h S.k fun j => S.alC (α j) := by
  intro l _ S m hm Φ hΦ
  obtain ⟨e, α, μ, hα, hμ, hΦd⟩ := phDec l S Φ hΦ
  let c : Fin e → Fin S.k.g → S.F := fun k j => μ k (m j)
  obtain ⟨u, ψ, hu, h1, h2⟩ := defUTest l S e α μ Φ hα hμ hΦd
  obtain ⟨u', hu', h1', h2'⟩ := defUConj l S.L S.G S.G0 S.h S.n S.x e u ψ
    (fun k => ∑ j, c k j • kapF S.h S.k j) hu
    (fun k => by rw [h1 k]; exact hm (μ k) (hμ k))
  obtain ⟨u'', ψ'', hu'', h1'', h2''⟩ := defUPush l S.L S.G S.G0 S.h S.n S.x S.k e u' ψ c hu' h1'
  have hL := defULift l S.L S.G S.G0 S.h S.n S.x S.k u'' ψ'' hu'' h1''
  refine ⟨fun j => ⟨∑ k, c k j • α k, Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hα k)⟩, ?_, ?_⟩
  · intro j b
    show (∑ k, c k j • α k) b = _
    rw [hΦd, add_sub_cancel_left]
    simp [c, mul_comm]
  · have e2 : (fun j => S.alC (∑ k, c k j • α k)) = epC' S.h S.x u'' := by
      funext j
      rw [h2'' j, (alSel l S).2.2.1 (Fin e) (fun k => c k j) α]
      simp only [h2', h2]
    show Lifts S.h S.k (fun j => S.alC (∑ k, c k j • α k))
    rw [e2]
    exact hL
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DualEx
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.exists_dual_functional_complement {R F N V : Type} [CommRing R] [IsLocalRing R] [Field F] [AddCommGroup N]
    [Module R N] [Module.Finite R N] [AddCommGroup V] [Module F V] {g : ℕ}
    (L : Submodule F (N →+ F)) (B : Submodule F V) (κ : Fin g → V) (T : (N →+ F) →ₗ[F] V) (φ : R →+* F)
    (hs : Function.Surjective φ)
    (hL : ∀ μ ∈ L, ∀ (b : R) y, μ (b • y) = φ b * μ y)
    (hK : ∀ μ ∈ L, ∃ c : Fin g → F, T μ - ∑ j, c j • κ j ∈ B)
    (hI : ∀ c : Fin g → F, ∑ j, c j • κ j ∈ B → c = 0)
    (hT : ∀ μ ∈ L, T μ ∈ B → μ = 0)
    [Module.Finite F L]
    (hsep : ∀ y : N, (∀ μ ∈ L, μ y = 0) → y ∈ maximalIdeal R • (⊤ : Submodule R N))
    (hD : ∀ ξ : Module.Dual F L, ∃ y : N, ∀ μ : L, (μ : N →+ F) y = ξ μ) :
    ∃ m : Fin g → N, (∀ μ ∈ L, T μ - ∑ j, μ (m j) • κ j ∈ B) ∧ Submodule.span R (Set.range m) = ⊤ := by
  classical
  have key : ∀ (a b : Fin g → F) (v : V), v - ∑ j, a j • κ j ∈ B → v - ∑ j, b j • κ j ∈ B → a = b := by
    intro a b v ha hb
    have h := hI (b - a) (by
      have e : ∑ j, (b - a) j • κ j = (v - ∑ j, a j • κ j) - (v - ∑ j, b j • κ j) := by
        simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
        abel
      rw [e]
      exact B.sub_mem ha hb)
    exact (sub_eq_zero.1 h).symm
  choose c hc using hK
  let C : L →ₗ[F] (Fin g → F) :=
    { toFun := fun μ => c μ μ.2
      map_add' := fun μ ν => by
        refine key _ _ _ (hc _ (μ + ν).2) ?_
        have e : T ((μ + ν : L) : N →+ F) - ∑ j, (c μ μ.2 + c ν ν.2) j • κ j
            = (T μ - ∑ j, c μ μ.2 j • κ j) + (T ν - ∑ j, c ν ν.2 j • κ j) := by
          simp only [Submodule.coe_add, map_add (f := _), Pi.add_apply, add_smul, Finset.sum_add_distrib]
          abel
        rw [e]
        exact B.add_mem (hc _ μ.2) (hc _ ν.2)
      map_smul' := fun a μ => by
        refine key _ _ _ (hc _ (a • μ).2) ?_
        have e : T ((a • μ : L) : N →+ F) - ∑ j, (a • c μ μ.2) j • κ j
            = a • (T μ - ∑ j, c μ μ.2 j • κ j) := by
          simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul, mul_smul, smul_sub,
            Finset.smul_sum]
        rw [RingHom.id_apply, e]
        exact B.smul_mem a (hc _ μ.2) }
  have hCinj : Function.Injective C := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro μ hμ
    have h0 : c μ μ.2 = 0 := hμ
    have h1 := hc μ μ.2
    rw [h0] at h1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, sub_zero] at h1
    exact Subtype.ext (hT μ μ.2 h1)
  have hCj : ∀ j, ∃ y : N, ∀ μ : L, (μ : N →+ F) y = C μ j := fun j => hD ((LinearMap.proj j).comp C)
  choose m hm using hCj
  refine ⟨m, fun μ hμ => ?_, ?_⟩
  · have e : ∀ j, μ (m j) = c μ hμ j := fun j => hm j ⟨μ, hμ⟩
    simp only [e]
    exact hc μ hμ
  · apply top_unique
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson ⊥)
    intro y _
    let ev : Module.Dual F L :=
      { toFun := fun μ => (μ : N →+ F) y
        map_add' := fun μ ν => rfl
        map_smul' := fun a μ => rfl }
    obtain ⟨ψ, hψ⟩ := LinearMap.dualMap_surjective_of_injective hCinj ev
    let a : Fin g → F := fun j => ψ fun i => if j = i then 1 else 0
    have hev : ∀ μ : L, (μ : N →+ F) y = ∑ j, C μ j * a j := by
      intro μ
      have h1 := LinearMap.congr_fun hψ μ
      rw [LinearMap.dualMap_apply, LinearMap.pi_apply_eq_sum_univ] at h1
      exact h1.symm
    let b : Fin g → R := fun j => Function.surjInv hs (a j)
    have hb : ∀ j, φ (b j) = a j := fun j => Function.surjInv_eq hs (a j)
    have hy : y - ∑ j, b j • m j ∈ maximalIdeal R • (⊤ : Submodule R N) := by
      apply hsep
      intro μ hμ
      have e : ∀ j, μ (m j) = C ⟨μ, hμ⟩ j := fun j => hm j ⟨μ, hμ⟩
      have ev2 : μ y = ∑ j, C ⟨μ, hμ⟩ j * a j := hev ⟨μ, hμ⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, ev2]
      simp only [hL μ hμ, hb, e]
      rw [sub_eq_zero]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have e : y = (y - ∑ j, b j • m j) + ∑ j, b j • m j := by abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_right hy) (Submodule.mem_sup_left ?_)
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem UpperTheory.V.Pa.dualEx :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), SelmerSpannedByKappaLaurent S.h S.k → ∃ m : Fin S.k.g → S.U.N, S.DualM m ∧ Submodule.span S.Bh (Set.range m) = ⊤ := by
  intro l _ S hK3
  haveI := S.d6
  haveI := S.U.fin
  haveI : Module.Finite S.Bh S.U.N := inferInstance
  let Bs : Submodule S.F (S.G.G₀ → Matrix (Fin S.n) (Fin S.n) S.F) :=
    { carrier := BdM S.h S.x S.F
      add_mem' := by
        rintro _ _ ⟨Y₁, h₁, t₁, rfl⟩ ⟨Y₂, h₂, t₂, rfl⟩
        refine ⟨Y₁ + Y₂, Submodule.add_mem _ h₁ h₂, by rw [Matrix.transpose_add, t₁, t₂, neg_add], ?_⟩
        funext g
        simp only [dY, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
        abel
      zero_mem' := ⟨0, Submodule.zero_mem _, by simp, by funext g; simp [dY]⟩
      smul_mem' := by
        rintro a _ ⟨Y, hY, t, rfl⟩
        refine ⟨a • Y, fun i j => ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩,
          by rw [Matrix.transpose_smul, t, smul_neg], ?_⟩
        · have h0 := (hY i j).1 hij
          rw [Submodule.mem_bot] at h0 ⊢
          simp [h0]
        · funext g
          simp only [dY, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_sub] }
  let T : (S.U.N →+ S.F) →ₗ[S.F] (S.G.G₀ → Matrix (Fin S.n) (Fin S.n) S.F) :=
    { toFun := S.laC
      map_add' := fun μ ν => by
        have h := (alSel l S).2.2.2 (Fin 2) ![1, 1] ![μ, ν]
        simpa [Fin.sum_univ_two] using h
      map_smul' := fun a μ => by
        have h := (alSel l S).2.2.2 Unit (fun _ => a) (fun _ => μ)
        simpa using h }
  have hs : Function.Surjective S.rF := fun z => by
    obtain ⟨o, ho⟩ := S.oo_surj z
    exact ⟨_, ho⟩
  obtain ⟨hfin, hsep, hD⟩ := laDual l S
  obtain ⟨m, h1, h2⟩ := UpperTheory.V.Pa.exists_dual_functional_complement (R := S.Bh) S.La Bs (kapF S.h S.k) T S.rF hs
    (fun μ hμ => hμ)
    (fun μ hμ => hK3 _ ((alSel l S).2.1 μ hμ).1 ((alSel l S).2.1 μ hμ).2)
    (indF l S.L S.G S.G0 S.h S.n S.x S.k) (laInj l S) hsep hD
  exact ⟨m, h1, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.FirstOrderLiftConstantPart
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {X : Type} [CommRing X] {g n : ℕ}

private def aH (X : Type) [CommRing X] (g : ℕ) : DD X g →+ X where
  toFun u := u.a
  map_zero' := rfl
  map_add' _ _ := rfl

private def epH (X : Type) [CommRing X] {g : ℕ} (j : Fin g) : DD X g →+ X where
  toFun u := u.ep j
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a :=
  map_sum (aH X g) f s

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (m : Fin g) :
    (∑ i ∈ s, f i).ep m = ∑ i ∈ s, (f i).ep m :=
  map_sum (epH X m) f s

private theorem sub_a (u v : DD X g) : (u - v).a = u.a - v.a := by
  rfl

private theorem sub_ep (u v : DD X g) (m : Fin g) : (u - v).ep m = u.ep m - v.ep m := by
  rfl

private theorem smul_a (c : X) (u : DD X g) : (c • u).a = c * u.a := rfl

private theorem smul_ep (c : X) (u : DD X g) (m : Fin g) : (c • u).ep m = c * u.ep m := by
  rw [Algebra.smul_def]
  show _ = _
  simp [DD.instAlgebra]
  rw [RingHom.algebraMap_toAlgebra]
  simp [DD.C]
  change c * u.ep m + (0 : Fin g → X) m * u.a = c * u.ep m
  simp

private theorem mul_mapa (P Q : Matrix (Fin n) (Fin n) (DD X g)) :
    (P * Q).map (fun u => u.a) = P.map (fun u => u.a) * Q.map (fun u => u.a) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, sum_a]
  rfl

private theorem mul_mapep (P Q : Matrix (Fin n) (Fin n) (DD X g)) (m : Fin g) :
    (P * Q).map (fun u => u.ep m) =
      P.map (fun u => u.a) * Q.map (fun u => u.ep m) + P.map (fun u => u.ep m) * Q.map (fun u => u.a) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, sum_ep, ← Finset.sum_add_distrib]
  rfl

private theorem sub_mapa (P Q : Matrix (Fin n) (Fin n) (DD X g)) :
    (P - Q).map (fun u => u.a) = P.map (fun u => u.a) - Q.map (fun u => u.a) := by
  ext a b
  simp [sub_a]

private theorem sub_mapep (P Q : Matrix (Fin n) (Fin n) (DD X g)) (m : Fin g) :
    (P - Q).map (fun u => u.ep m) = P.map (fun u => u.ep m) - Q.map (fun u => u.ep m) := by
  ext a b
  simp [sub_ep]

end SlopeTestRemainingChoices

private theorem first_order_lift_constant_part {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X]
    [Algebra x.A X] (γ : F.G₀) : (k.ρ1 X γ).map (fun u => u.a) = x.ρX X γ := by
  unfold Kap.ρ1
  rw [mul_mapa]
  have h1 : (1 + DD.epM fun j => (k.κ j γ).map (algebraMap x.A X)).map (fun u : DD X k.g => u.a) =
      (1 : Matrix (Fin n) (Fin n) X) := by
    ext i j
    rw [Matrix.map_apply, Matrix.add_apply]
    change ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) i j).a + 0 = (1 : Matrix (Fin n) (Fin n) X) i j
    rw [add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rfl
    · rfl
  have h2 : (x.ρX (DD X k.g) γ).map (fun u => u.a) = x.ρX X γ := by
    ext i j
    rfl
  rw [h1, h2, one_mul]

end UpperTheory.V.Pa

private theorem card_le_of_linearIndependent_mod_bd1_in_sel1 {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ}
    {x : NP G0.frame n} (k : Kap x) (D0 : ℕ) (hK : SelmerRankBoundLaurent h k D0) {ι : Type} [Fintype ι]
    (z : ι → G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr k.g))
    (hz : ∀ i, z i ∈ Sel1 h x.Fr k ∧ BndD x.t (z i))
    (hind : ∀ c : ι → x.Fr, ∑ i, c i • z i ∈ Bd1 h x.Fr k → c = 0) : Fintype.card ι ≤ D0 := by
  let q := Fintype.equivFin ι
  refine hK _ (fun j => z (q.symm j)) (fun j => hz _) ?_
  intro c hc
  have h0 : (fun i => c (q i)) = 0 := by
    apply hind
    have hs : ∑ i, c (q i) • z i = ∑ j, c j • z (q.symm j) := by
      rw [← Equiv.sum_comp q (fun j => c j • z (q.symm j))]
      simp
    rw [hs]
    exact hc
  funext j
  have := congrFun h0 (q.symm j)
  simpa using this

private theorem map_a_rho1_mul_mul_sub_eq {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (γ δ : F.G₀) (Y : Matrix (Fin n) (Fin n) (DD X k.g)) :
    (k.ρ1 X γ * Y * k.ρ1 X δ - Y).map (fun u => u.a) =
      x.ρX X γ * Y.map (fun u => u.a) * x.ρX X δ - Y.map (fun u => u.a) := by
  rw [sub_mapa, mul_mapa, mul_mapa, first_order_lift_constant_part, first_order_lift_constant_part]

private theorem map_ep_rho1_mul_mul_sub_eq_of_map_a_eq_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (γ δ : F.G₀) (Y : Matrix (Fin n) (Fin n) (DD X k.g)) (m : Fin k.g)
    (hY : Y.map (fun u => u.a) = 0) :
    (k.ρ1 X γ * Y * k.ρ1 X δ - Y).map (fun u => u.ep m) =
      x.ρX X γ * Y.map (fun u => u.ep m) * x.ρX X δ - Y.map (fun u => u.ep m) := by
  rw [sub_mapep, mul_mapep, mul_mapep, mul_mapa, hY, first_order_lift_constant_part, first_order_lift_constant_part]
  simp

private theorem dd_a_add_of_commRing {X : Type} [CommRing X] {g : ℕ} (u v : DD X g) : (u + v).a = u.a + v.a := rfl

private theorem dd_ep_add_apply {X : Type} [CommRing X] {g : ℕ} (u v : DD X g) (m : Fin g) :
    (u + v).ep m = u.ep m + v.ep m := rfl

theorem UpperTheory.V.Pa.claim1 :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ D0, SelmerRankBoundLaurent S.h S.k D0 → ∀ (e : ℕ) (α : Fin e → S.Tp), LinearIndependent S.F α → (∀ i j, Lifts S.h S.k (Pi.single j (S.alC (α i)))) → e + S.k.g * S.k.g ≤ D0 := by
  intro l _ S D0 hK e α hα hl
  classical
  have hsel : ∀ i, S.alC (α i) ∈ SelP S.h S.x S.F ∧ BndM S.x.t (S.alC (α i)) :=
    fun i => (alSel l S).1 _ (α i).2
  choose y hy1 hy2 hy3 using fun i => lift1 l S.L S.G S.G0 S.h S.n S.x S.k _ (hsel i).1 (hsel i).2 (hl i)
  have hy4 : ∀ i γ a b, (y i γ a b).a = S.alC (α i) γ a b := by
    intro i γ a b
    rw [← hy3]
    rfl
  let w : Fin S.k.g × Fin S.k.g → S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.x.Fr S.k.g) :=
    fun p γ => DD.epM (Pi.single p.2 (kapF S.h S.k p.1 γ))
  have hw0 : ∀ p γ a b, (w p γ a b).a = 0 := fun _ _ _ _ => rfl
  let z : Fin e ⊕ (Fin S.k.g × Fin S.k.g) → S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.x.Fr S.k.g) :=
    Sum.elim y w
  have hz : ∀ i, z i ∈ Sel1 S.h S.x.Fr S.k ∧ BndD S.x.t (z i) := by
    rintro (i | p)
    · exact ⟨hy1 i, hy2 i⟩
    · exact kapSel1 l S.L S.G S.G0 S.h S.n S.x S.k p.1 p.2
  have hind : ∀ c : Fin e ⊕ (Fin S.k.g × Fin S.k.g) → S.x.Fr,
      ∑ i, c i • z i ∈ Bd1 S.h S.x.Fr S.k → c = 0 := by
    intro c hc
    obtain ⟨Y, hYW, hYt, hYeq⟩ := hc
    have hsum : ∑ i, c i • z i = ∑ i, c (Sum.inl i) • y i + ∑ p, c (Sum.inr p) • w p := by
      rw [Fintype.sum_sum_type]
      rfl
    rw [hsum] at hYeq
    have hA : ∀ γ, (∑ i, c (Sum.inl i) • S.alC (α i)) γ =
        S.x.ρX S.x.Fr (S.h.p₀ γ) * Y.map (fun u => u.a) * S.x.ρX S.x.Fr (S.h.p₀ γ⁻¹) -
          Y.map (fun u => u.a) := by
      intro γ
      have e1 := congrArg (fun M => M.map (fun u : DD S.x.Fr S.k.g => u.a)) (congrFun hYeq γ)
      simp only [dY] at e1
      rw [map_a_rho1_mul_mul_sub_eq] at e1
      rw [← e1]
      ext a b
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Matrix.map_apply, Matrix.add_apply,
        Matrix.sum_apply, Matrix.smul_apply, dd_a_add_of_commRing, sum_a, smul_a, hy4, hw0, smul_eq_mul, mul_zero,
        Finset.sum_const_zero, add_zero]
    have hnegA : ∀ u : DD S.x.Fr S.k.g, (-u).a = -u.a := fun u => map_neg (aH S.x.Fr S.k.g) u
    have hTA : (Y.map (fun u => u.a))ᵀ = -(Y.map (fun u => u.a)) := by
      rw [← Matrix.transpose_map, hYt]
      ext a b
      simp only [Matrix.map_apply, Matrix.neg_apply, hnegA]
    have hEv : Y.map (fun u => u.a) ∈ Ev S.x.A S.x.Fr S.n S.x.a := by
      intro a b
      refine ⟨fun _ => Submodule.mem_top, fun hab => ?_⟩
      have h1 := ((hYW a b).2 hab).1 rfl
      exact (Submodule.mem_bot _).2 h1
    have hmem : ∑ i, c (Sum.inl i) • (α i : S.Bh →+ S.F) ∈ S.Tp :=
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (α i).2)
    have hBd : S.alC (∑ i, c (Sum.inl i) • (α i : S.Bh →+ S.F)) ∈ BdP S.h S.x S.F := by
      rw [(alSel l S).2.2.1 (Fin e) (fun i => c (Sum.inl i)) (fun i => (α i : S.Bh →+ S.F))]
      refine ⟨Y.map (fun u => u.a), hEv, hTA, ?_⟩
      funext γ
      exact hA γ
    have hz0 := alInj l S _ hmem hBd
    have hc1 : ∀ i, c (Sum.inl i) = 0 := by
      refine Fintype.linearIndependent_iff.1 hα (fun i => c (Sum.inl i)) ?_
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simpa using hz0
    have hYa : Y.map (fun u => u.a) = 0 := by
      refine invEv l S.L S.G S.G0 S.h S.n S.x S.odd _ hEv hTA ?_
      intro γ
      simp only [dY]
      rw [← hA γ]
      simp [hc1]
    have hEp : ∀ m : Fin S.k.g, ∀ γ, (∑ i, c (Sum.inr (i, m)) • kapF S.h S.k i) γ =
        S.x.ρX S.x.Fr (S.h.p₀ γ) * Y.map (fun u => u.ep m) * S.x.ρX S.x.Fr (S.h.p₀ γ⁻¹) -
          Y.map (fun u => u.ep m) := by
      intro m γ
      have e1 := congrArg (fun M => M.map (fun u : DD S.x.Fr S.k.g => u.ep m)) (congrFun hYeq γ)
      simp only [dY] at e1
      rw [map_ep_rho1_mul_mul_sub_eq_of_map_a_eq_zero _ _ _ _ _ _ hYa] at e1
      rw [← e1]
      ext a b
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Matrix.map_apply, Matrix.add_apply,
        Matrix.sum_apply, Matrix.smul_apply, dd_ep_add_apply, sum_ep, smul_ep, hc1, zero_mul,
        Finset.sum_const_zero, zero_add, smul_eq_mul]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hw : ∀ j, (w (i, j) γ a b).ep m = if m = j then kapF S.h S.k i γ a b else 0 := by
        intro j
        show (Pi.single j (kapF S.h S.k i γ) : Fin S.k.g → _) m a b = _
        rw [Pi.single_apply]
        split_ifs
        · rfl
        · rfl
      simp only [hw, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hd : ∀ m, (fun i => c (Sum.inr (i, m))) = 0 := by
      intro m
      have hnegE : ∀ u : DD S.x.Fr S.k.g, (-u).ep m = -u.ep m := fun u => map_neg (epH S.x.Fr m) u
      apply indF l S.L S.G S.G0 S.h S.n S.x S.k
      refine ⟨Y.map (fun u => u.ep m), ?_, ?_, ?_⟩
      · intro a b
        refine ⟨fun hab => ?_, fun _ => Submodule.mem_top⟩
        have h1 := ((hYW a b).1 hab).2.1 rfl
        exact (Submodule.mem_bot _).2 (congrFun h1 m)
      · rw [← Matrix.transpose_map, hYt]
        ext a b
        simp only [Matrix.map_apply, Matrix.neg_apply, hnegE]
      · funext γ
        exact hEp m γ
    funext s
    rcases s with i | p
    · exact hc1 i
    · exact congrFun (hd p.2) p.1
  have := card_le_of_linearIndependent_mod_bd1_in_sel1 S.h S.k D0 hK z hz hind
  simpa using this
end

