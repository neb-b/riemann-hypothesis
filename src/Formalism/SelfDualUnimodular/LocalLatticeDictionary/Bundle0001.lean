module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0004
public import Lemmata.Denominators.Denom
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0003

@[expose] public section

-- bundled from Formalism.SelfDualUnimodular.LocalLatticeDictionary.LocFin
section
noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.LF

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem vec_denom (M : Submodule (𝓞 E) (Fin n → E)) (hsp : Submodule.span E (M : Set (Fin n → E)) = ⊤)
    (v : Fin n → E) : ∃ m : ℕ, 0 < m ∧ (m : 𝓞 E) • v ∈ M := by
  first | exact Bl.DenominatorsAlt.goal1 .. | (apply Bl.DenominatorsAlt.goal1 <;> assumption) | (intros; apply Bl.DenominatorsAlt.goal1 <;> assumption)

theorem lat_denom (L M : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hsp : Submodule.span E (M : Set (Fin n → E)) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, (N : 𝓞 E) • x ∈ M := by
  classical
  obtain ⟨S, hS⟩ := hL
  choose f hf0 hfM using fun v : Fin n → E => vec_denom M hsp v
  refine ⟨∏ s ∈ S, f s, Finset.prod_pos (fun i _ => hf0 i), ?_⟩
  intro x hx
  rw [← hS] at hx
  have hle : Submodule.span (𝓞 E) (S : Set (Fin n → E)) ≤
      M.comap (((∏ s ∈ S, f s : ℕ) : 𝓞 E) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro s hs
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.mp hs)
    rw [hk, Nat.cast_mul, mul_comm, mul_smul]
    exact M.smul_mem _ (hfM s)
  have h2 := hle hx
  rwa [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at h2

theorem loc_le_of_denom {L M : Submodule (𝓞 E) (Fin n → E)} {N : ℕ} (hN : ∀ x ∈ L, (N : 𝓞 E) • x ∈ M)
    {p : Ideal (𝓞 E)} (hp : p.IsPrime) (hNp : (N : 𝓞 E) ∉ p) :
    Formalism.HermitianLatticesTheory.loc (K := E) p L ≤ Formalism.HermitianLatticesTheory.loc (K := E) p M := by
  rintro x ⟨t, ht, htx⟩
  have hNh : (N : 𝓞 E) ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p := by
    rw [mem_hcompl_iff hp, mem_conjIdeal_iff, map_natCast]
    exact ⟨hNp, hNp⟩
  refine ⟨(N : 𝓞 E) * t, mul_mem hNh ht, ?_⟩
  rw [mul_smul]; exact hN _ htx

theorem lattice_locally_finite : LocFinite := by
  intro E _ _ _ n L M hLfg hMfg hLsp hMsp
  obtain ⟨N₁, hN₁, h1⟩ := lat_denom L M hLfg hMsp
  obtain ⟨N₂, hN₂, h2⟩ := lat_denom M L hMfg hLsp
  have h0 : ((N₁ * N₂ : ℕ) : 𝓞 E) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact (Nat.mul_pos hN₁ hN₂).ne'
  refine (Ring.HasFiniteQuotients.finite_setOfPred_mem _ h0).subset ?_
  rintro p ⟨hp, hne⟩
  by_contra hNp
  apply hne
  have hp' := hp.isPrime
  simp only [Set.mem_ofPred_eq, Nat.cast_mul] at hNp
  have n1 : (N₁ : 𝓞 E) ∉ p := fun h => hNp (p.mul_mem_right _ h)
  have n2 : (N₂ : 𝓞 E) ∉ p := fun h => hNp (p.mul_mem_left _ h)
  exact le_antisymm (loc_le_of_denom h2 hp' n2) (loc_le_of_denom h1 hp' n1)

end Formalism.L2.SG.Pf.LatDictZ.Z0.LF
end
end

-- bundled from Formalism.SelfDualUnimodular.LocalLatticeDictionary.UnimodOfSelfDual
section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.BR

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def hJ (J : Matrix (Fin n) (Fin n) E) : (Fin n → E) →ₗ⋆[E] (Fin n → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => Formalism.UG.hform (starRingEnd E) J x y)
    (by
      intro x y z
      simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib])
    (by
      intro c x y
      simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (by
      intro x y z
      simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (by
      intro c x y
      simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem hJ_apply (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hJ J x y = Formalism.UG.hform (starRingEnd E) J x y := rfl

theorem hJ_symm {J : Matrix (Fin n) (Fin n) E} (hJh : Formalism.UG.IsHerm (starRingEnd E) J) :
    (hJ J).IsSymm := by
  have hJij : ∀ i j, starRingEnd E (J j i) = J i j := fun i j => by
    have := congrFun (congrFun hJh i) j
    simpa [Formalism.UG.cT] using this
  refine ⟨fun x y => ?_⟩
  change starRingEnd E (Formalism.UG.hform (starRingEnd E) J x y) = Formalism.UG.hform (starRingEnd E) J y x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_self_apply, hJij]
  ring

theorem hJ_single (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (j : Fin n) :
    hJ J x (Pi.single j 1) = (Matrix.vecMul (fun i => starRingEnd E (x i)) J) j := by
  rw [hJ_apply, Formalism.UG.hform, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem hJ_nondeg {J : Matrix (Fin n) (Fin n) E} (hdet : J.det ≠ 0) (x : Fin n → E)
    (hx : ∀ y, hJ J x y = 0) : x = 0 := by
  have h0 : Matrix.vecMul (fun i => starRingEnd E (x i)) J = 0 := by
    funext j; rw [← hJ_single]; exact hx _
  have h1 := Matrix.eq_zero_of_vecMul_eq_zero hdet h0
  funext i
  have := congrFun h1 i
  simpa using this

theorem star_int (r : 𝓞 E) : star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
  ⟨conjO E r, algebraMap_conjO r⟩

theorem unimod_of_selfDual {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : SelfDual J L) : Formalism.HermitianLatticesTheory.IsUnimodular (hJ J) L := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  ext x
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  rw [hL x]
  constructor
  · intro h y hy
    obtain ⟨r, hr⟩ := h y hy
    exact ⟨r, hr⟩
  · intro h y hy
    obtain ⟨r, hr⟩ := h y hy
    exact ⟨r, hr⟩

theorem selfDualMod_loc {J : Matrix (Fin n) (Fin n) E} (hJh : Formalism.UG.IsHerm (starRingEnd E) J)
    {L : Submodule (𝓞 E) (Fin n → E)} (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hL : SelfDual J L) {p : Ideal (𝓞 E)} (hp : p.IsMaximal) :
    IsSelfDualMod (locRing p) (hJ J) (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup := by
  have hu := (Formalism.HermitianLatticesTheory.locDual (𝓞 E) E (Fin n → E) (hJ J) (hJ_symm hJh) star_int L hfg).2.1
    (unimod_of_selfDual hL) p hp
  have hfull : Submodule.IsFullLattice E L :=
    { toIsLattice := Submodule.IsLattice.of_fg E hfg
      span_eq_top := hsp }
  exact isSelfDualMod_loc hfull hp.isPrime hu

theorem gl_of_isom {J : Matrix (Fin n) (Fin n) E} (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hg : ∀ x y, hJ J (g x) (g y) = hJ J x y) :
    ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ (starRingEnd E) J ∧ ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w := by
  let A := LinearMap.toMatrix' (g : (Fin n → E) →ₗ[E] (Fin n → E))
  let B := LinearMap.toMatrix' (g.symm : (Fin n → E) →ₗ[E] (Fin n → E))
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g : (Fin n → E) →ₗ[E] (Fin n → E)) ∘ₗ (g.symm : (Fin n → E) →ₗ[E] (Fin n → E)) = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g.symm : (Fin n → E) →ₗ[E] (Fin n → E)) ∘ₗ (g : (Fin n → E) →ₗ[E] (Fin n → E)) = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  let γ : GL (Fin n) E := ⟨A, B, hAB, hBA⟩
  have hmul : ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w := fun w => by
    change A *ᵥ w = g w
    rw [LinearMap.toMatrix'_mulVec]; rfl
  refine ⟨γ, ?_, hmul⟩
  change Formalism.UG.cT (starRingEnd E) A * J * A = J
  ext i j
  have e1 := hg (Pi.single i 1) (Pi.single j 1)
  have hsingle : ∀ k l, hJ J (Pi.single k 1) (Pi.single l 1) = J k l := by
    intro k l
    rw [hJ_single, Matrix.vecMul, dotProduct]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  rw [hsingle] at e1
  rw [← e1, hJ_apply, Formalism.UG.hform]
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  have hcol : ∀ k l, A k l = g (Pi.single l 1) k := fun k l => by
    simp [A, LinearMap.toMatrix'_apply]
  simp only [hcol, Finset.sum_mul]
  rw [Finset.sum_comm]

end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
end
end

