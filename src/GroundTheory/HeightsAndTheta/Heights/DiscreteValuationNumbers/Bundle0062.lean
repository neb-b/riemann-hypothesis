module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AevalEqOfVdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagDegreeZero

theorem le_weight_block {κ : Type} [DecidableEq κ] {τ : κ → Type} (c : (Σ o, τ o) →₀ ℕ) {p : Σ o, τ o}
    (hp : p ∈ c.support) : c p ≤ Finsupp.weight (blockWeight τ) c p.1 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  refine le_trans (le_of_eq ?_)
    (Finset.single_le_sum (f := fun x => (c x • blockWeight τ x) p.1) (fun _ _ => Nat.zero_le _) hp)
  simp [blockWeight]

theorem aeval_eq_of_vdeg {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] {M M' : ℕ}
    {Φ : Type} [Field Φ] [Algebra O Φ] {z z' : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ}
    (h : ∀ (k : K) (i : ι k), z ⟨some (some k), i⟩ = z' ⟨some (some k), i⟩)
    {G : MRing (bundleIdx (bundleIdx ι M) M') O} {β : K → ℕ} (hG : IsMultiHomog G (GenericProjClosureDivisor.vdeg β)) :
    aeval z G = aeval z' G := by
  rw [aeval_def, aeval_def]
  apply eval₂_congr
  intro p c' hp hc
  obtain ⟨o, i⟩ := p
  have key := le_weight_block c' hp
  rw [hG hc] at key
  rcases o with _ | _ | k
  · simp [GenericProjClosureDivisor.vdeg] at key
    exact absurd key (Finsupp.mem_support_iff.mp hp)
  · simp [GenericProjClosureDivisor.vdeg] at key
    exact absurd key (Finsupp.mem_support_iff.mp hp)
  · exact h k i

theorem flag_eq_zero {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N : ℕ} (w e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (χ : Module.Dual Ω E) {k : ℕ}
    (h0 : ∑ j, flagCoord w e t k j * algebraMap Ω Φ (χ (w j)) = 0) (j : Fin N) (hj : (j : ℕ) < k) :
    χ (w j) = 0 := by
  let θ : Module.Dual Ω E := ∑ j : Fin N, (if (j : ℕ) < k then χ (w j) else 0) • w.coord j
  have hθe : ∀ i, θ (e i) = ∑ j : Fin N, (if (j : ℕ) < k then χ (w j) else 0) * w.repr (e i) j := by
    intro i
    simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  have hθ : θ = 0 := by
    refine e.ext fun i => ?_
    have key := Fintype.linearIndependent_iff.1 ht (fun i => θ (e i)) (by
      rw [← h0]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hθe, Algebra.smul_def, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [flagCoord]
      split_ifs
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        ring
      · simp)
    simpa using key i
  have h := congrArg (fun f : Module.Dual Ω E => f (w j)) hθ
  simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, LinearMap.zero_apply] at h
  rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)] at h
  simpa [hj] using h

end SegreFlagDegreeZero


open GenericProjClosureDivisor SegreFlagClosureModel SegreFlagDegreeZero in
theorem SegreFlagDegreeZero.proof (hModel : SegreFlagClosureModel.Statement) : SegreFlagDegreeZero.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hkN
  obtain ⟨hZ, f₀, g₀, hD₀, hv₀⟩ := hModel O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ'
    hφ hφ' Φ e t ht (k + 1) (by omega) (by omega)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨f₀, g₀, hD₀, hv₀, fun h => absurd h (lt_irrefl 0)⟩
  unfold flagClosurePt at hZ hD₀ hv₀ ⊢

  have hne : ∀ κ, ∃ j, y ⟨κ, j⟩ ≠ 0 := fun κ => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant κ
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun κ _ => hc κ
  have hli := ht.linearIndependent
  obtain ⟨m, hm⟩ := exists_flag_ne_zero w e hli φ'
    (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc) (by omega) hkN.le
  have hϖΩ : algebraMap O Ω ϖ ≠ 0 := by
    intro h0
    have hy : ϖ ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, h0,
        map_zero]
    rw [hV.noTorsion] at hy
    exact hϖ.ne_zero (by simpa using hy)

  obtain ⟨n, r, hr, hx⟩ :=
    TwistedDualGensExpress.proof O ϖ Ω K ι y N E B B' hB a₀ a₀' M M' φ φ' hφ hφ' c hyc m
  obtain ⟨bG, bH, G, hG, hdeg, hval⟩ :=
    express_forms (M := M) (M' := M') y w φ φ' (flagCoord w e t (k + 1)) c hyc ϖ φ (φ' m) a₀ a₀' n r hr hx
  obtain ⟨H, hHdef⟩ : ∃ H : MRing (bundleIdx (bundleIdx ι M) M') O, H = C (ϖ ^ n) * chartMonoZ O M M' c bH :=
    ⟨_, rfl⟩
  rw [← hHdef] at hval
  have hHhom : IsMultiHomog H (vdeg bH) := by
    have := (isWeightedHomogeneous_C (blockWeight (bundleIdx (bundleIdx ι M) M')) (ϖ ^ n)).mul
      (chartMonoZ_homog (O := O) (M := M) (M' := M') c bH)
    rw [hHdef]
    rwa [zero_add] at this

  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Ω, ∀ (κ : K) (i : ι κ),
      y₀ ⟨some (some κ), i⟩ = y ⟨κ, i⟩ := ⟨pairProjCoord y w φ φ' (0 : Fin N → Ω), fun κ i => by
        simp [pairProjCoord, projCoord]⟩
  have hV' : ∀ {β : K → ℕ} {F : MRing (bundleIdx (bundleIdx ι M) M') O}, IsMultiHomog F (vdeg β) →
      ∀ u : Fin N → Φ, aeval (pairProjCoord y w φ φ' u) F = algebraMap Ω Φ (aeval y₀ F) := by
    intro β F hF u
    rw [← MvPolynomial.aeval_algebraMap_apply]
    exact aeval_eq_of_vdeg (fun κ i => by simp [pairProjCoord, projCoord, hy₀]) hF

  obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual Ω E, χ = aeval y₀ H • φ' m - ∑ l, aeval y₀ (G l) • φ l := ⟨_, rfl⟩
  have hχgen : ∀ u : Fin N → Φ, genVal w u χ = algebraMap Ω Φ (aeval y₀ H) * genVal w u (φ' m) -
      ∑ l, algebraMap Ω Φ (aeval y₀ (G l)) * genVal w u (φ l) := by
    intro u
    have hsub : ∀ ψ₁ ψ₂ : Module.Dual Ω E, genVal w u (ψ₁ - ψ₂) = genVal w u ψ₁ - genVal w u ψ₂ := by
      intro ψ₁ ψ₂
      simp only [genVal, LinearMap.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
    rw [hχ, hsub, genVal_smul]
    simp only [genVal_sum_smul]
  have h1 : genVal w (flagCoord w e t (k + 1)) χ = 0 := by
    simp only [hV' hHhom, hV' (hG _)] at hval
    rw [hχgen, hval, sub_self]
  have hχw := flag_eq_zero w e hli χ h1
  have hvanish : ∀ ψ : Module.Dual Ω E, (∀ j : Fin N, (j : ℕ) < k + 1 → ψ (w j) = 0) →
      genVal w (flagCoord w e t k) ψ = 0 := by
    intro ψ hψ
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [flagCoord]
    split_ifs with hj
    · rw [hψ j (by omega), map_zero, mul_zero]
    · rw [zero_mul]
  have hid : ∀ u : Fin N → Φ, genVal w u χ = 0 → aeval (pairProjCoord y w φ φ' u) H * genVal w u (φ' m) =
      ∑ l, aeval (pairProjCoord y w φ φ' u) (G l) * genVal w u (φ l) := by
    intro u hu
    rw [hχgen, sub_eq_zero] at hu
    simp only [hV' hHhom, hV' (hG _)]
    exact hu

  have hval3 : ∀ u : Fin N → Φ, genVal w u χ = 0 → aeval (pairProjCoord y w φ φ' u) (∑ l, X ⟨some none, l⟩ * G l) =
      aeval (pairProjCoord y w φ φ' u) (X ⟨none, m⟩ * H) := fun u hu =>
    val_pair (z := pairProjCoord y w φ φ' u) (v := fun l => genVal w u (φ l)) (w := genVal w u (φ' m))
      (fun l => aeval_X _ _) G (aeval_X _ _) H (hid u hu)
  have hHne : ∀ u : Fin N → Φ, aeval (pairProjCoord y w φ φ' u) H ≠ 0 := by
    intro u
    rw [hHdef, map_mul, aeval_C, aeval_chartMonoZ, IsScalarTower.algebraMap_apply O Ω Φ]
    refine mul_ne_zero ((map_ne_zero _).mpr (by rw [map_pow]; exact pow_ne_zero _ hϖΩ))
      ((map_ne_zero _).mpr (Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hc κ)))
  have hgv : ∀ u : Fin N → Φ, genVal w u (φ' m) ≠ 0 → aeval (pairProjCoord y w φ φ' u) (X ⟨none, m⟩ * H) ≠ 0 := by
    intro u hu
    rw [map_mul, aeval_X]
    exact mul_ne_zero hu (hHne u)
  have hs₁ : genVal w (flagCoord w e t (k + 1)) (φ' m) ≠ 0 := by
    intro h0
    exact hm (hvanish (φ' m) (flag_eq_zero w e hli (φ' m) h0))
  have hout : ∀ u : Fin N → Φ, genVal w u χ = 0 → genVal w u (φ' m) ≠ 0 →
      (∑ l, X ⟨some none, l⟩ * G l) ∉ pointIdeal O (pairProjCoord y w φ φ' u) ∧
        X ⟨none, m⟩ * H ∉ pointIdeal O (pairProjCoord y w φ φ' u) := by
    intro u hu hu'
    refine ⟨fun hm' => hgv u hu' ?_, fun hm' => hgv u hu' (aeval_eq_zero_of_mem hm')⟩
    rw [← hval3 u hu]
    exact aeval_eq_zero_of_mem hm'

  have hdeg3 : ∃ bf bg : Option (Option K) → ℕ, IsMultiHomog (∑ l, X ⟨some none, l⟩ * G l) bf ∧
      IsMultiHomog (X ⟨none, m⟩ * H) bg ∧ (fun o => (bf o : ℤ) - bg o) = zetaFirst a₀ - zetaSecond a₀' := by
    refine ⟨Pi.single (some none) 1 + vdeg bG, Pi.single none 1 + vdeg bH, ?_, ?_, ?_⟩
    · exact IsWeightedHomogeneous.sum _ _ _ fun l _ =>
        IsWeightedHomogeneous.mul (isWeightedHomogeneous_X O _ _) (hG l)
    · exact IsWeightedHomogeneous.mul
        (isWeightedHomogeneous_X O (blockWeight (bundleIdx (bundleIdx ι M) M')) ⟨none, m⟩) hHhom
    · funext o
      rcases o with _ | _ | κ
      · simp [vdeg, zetaFirst, zetaSecond]
      · simp [vdeg, zetaFirst, zetaSecond]
      · simp [vdeg, zetaFirst, zetaSecond]
        linarith [hdeg κ]

  have hP1 : (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t (k + 1)))).IsPrime := hZ.multiProj.isPrime
  have hcross := IsZPair.cross (⟨hD₀.degrees, hv₀⟩ : IsZPair a₀ a₀' _ f₀ g₀) (⟨hdeg3, hval3 _ h1⟩ : IsZPair a₀ a₀' _ _ _)
  obtain ⟨hf1, hg1⟩ := hout _ h1 hs₁
  obtain ⟨hf0, hg0⟩ := hout _ (hvanish χ hχw) hm
  refine ⟨_, _, IsVerticalDivisor.of_unit_off_special hdeg3 hf1 hg1 ?_, hval3 _ h1,
    fun _ => ⟨hf0, hg0, hval3 _ (hvanish χ hχw)⟩⟩
  intro W hW hPW hWr hϖW
  obtain ⟨u, v, hu, hv, huv⟩ := hD₀.unit_off_special W hW hPW hWr hϖW
  refine ⟨u, v, hu, hv, ?_⟩
  have hmem : g₀ * (u * (∑ l, X ⟨some none, l⟩ * G l) - v * (X ⟨none, m⟩ * H)) ∈
      pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) := by
    rw [show g₀ * (u * (∑ l, X ⟨some none, l⟩ * G l) - v * (X ⟨none, m⟩ * H)) =
      (X ⟨none, m⟩ * H) * (u * f₀ - v * g₀) - u * (f₀ * (X ⟨none, m⟩ * H) - (∑ l, X ⟨some none, l⟩ * G l) * g₀) by ring]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ huv) (Ideal.mul_mem_left _ _ hcross)
  exact (hP1.mem_or_mem hmem).resolve_left hD₀.den_not_mem

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsLocFrac
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 TensorProduct

section Restrict

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def genPt (F : Type*) [Field F] (Q : Ideal (MRingOver F ι)) :
    (Σ k, ι k) → FractionRing (MRingOver F ι ⧸ Q) :=
  fun p => algebraMap (MRingOver F ι ⧸ Q) _ (Ideal.Quotient.mk Q (X p))

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]

def IsLocFrac (Q : Ideal (MRingOver (kap O) ι)) (F G : MRingOver O ι) : Prop :=
  ∃ α : K → ℕ, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F α ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G α ∧ MvPolynomial.map (IsLocalRing.residue O) G ∉ Q

def stalk (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) : AddSubgroup V :=
  AddSubgroup.closure {v | ∃ F G : MRingOver O ι, IsLocFrac O Q F G ∧ ∃ s, mseg (genPt (kap O) Q) s ≠ 0 ∧
    ∃ e ∈ B.lat s, v = (aeval x F / aeval x G) • e}

def resRel (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) :
    Set (FractionRing (MRingOver (kap O) ι ⧸ Q) ⊗[ℤ] stalk O x Q B) :=
  {t | ∃ F G : MRingOver O ι, IsLocFrac O Q F G ∧ ∃ m m' : stalk O x Q B,
    (m' : V) = (aeval x F / aeval x G) • (m : V) ∧
    t = (aeval (genPt (kap O) Q) (MvPolynomial.map (IsLocalRing.residue O) F) /
        aeval (genPt (kap O) Q) (MvPolynomial.map (IsLocalRing.residue O) G)) ⊗ₜ m - 1 ⊗ₜ m'}

abbrev resFibre (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) :=
  (FractionRing (MRingOver (kap O) ι ⧸ Q) ⊗[ℤ] stalk O x Q B) ⧸
    Submodule.span (FractionRing (MRingOver (kap O) ι ⧸ Q)) (resRel O x Q B)

def resMap (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) : stalk O x Q B →+ resFibre O x Q B :=
  (Submodule.mkQ _).toAddMonoidHom.comp
    (TensorProduct.mk ℤ (FractionRing (MRingOver (kap O) ι ⧸ Q)) (stalk O x Q B) 1).toAddMonoidHom

def resLat (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) (s : ∀ k, ι k) : AddSubgroup (resFibre O x Q B) :=
  ((B.lat s).addSubgroupOf (stalk O x Q B)).map (resMap O x Q B)

def resSub (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) (W : Submodule Ω V) :
    Submodule (FractionRing (MRingOver (kap O) ι ⧸ Q)) (resFibre O x Q B) :=
  Submodule.span _ (resMap O x Q B '' {m | (m : V) ∈ W})

end Restrict

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle MRingOver)

def FullFlagRestriction.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N : ℕ)
    (V : Type) [AddCommGroup V] [Module Ω V] (B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    ∀ (Q : Ideal (MRingOver (IsLocalRing.ResidueField O) ι)) [Q.IsPrime], ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) ≤ Q →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal (IsLocalRing.ResidueField O)
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) Q) = Q ∧
      ∃ B' : ChartBundle (IsLocalRing.ResidueField O)
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) Q)) N
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.resFibre O x Q B),
        B'.lat = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.resLat O x Q B ∧
        ∀ fl : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FullFlag O x B,
          ∃ fl' : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FullFlag (IsLocalRing.ResidueField O)
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) Q) B',
            fl'.deg = fl.deg ∧ ∀ i, fl'.Vs i = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.resSub O x Q B (fl.Vs i)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpColonFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem pow_add_mul_eq_span_pow_mul {A : Type*} [CommRing A] {I : Ideal A} {k n₀ : ℕ} {y : A}
    (h : I ^ (n₀ + k) = Ideal.span {y} * I ^ n₀) (s : ℕ) :
    I ^ (n₀ + k * s) = Ideal.span {y ^ s} * I ^ n₀ := by
  have hprop : ∀ t, I ^ (n₀ + t + k) = Ideal.span {y} * I ^ (n₀ + t) := by
    intro t
    induction t with
    | zero => simpa using h
    | succ t ih =>
      rw [show n₀ + (t + 1) + k = n₀ + t + k + 1 by omega, pow_succ, ih,
        show n₀ + (t + 1) = n₀ + t + 1 by omega, pow_succ, mul_assoc]
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show n₀ + k * (s + 1) = n₀ + k * s + k by ring, hprop, ih, ← mul_assoc,
      Ideal.span_singleton_mul_span_singleton, ← pow_succ']

theorem mem_div_self_mul_of_mem_div_self {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]
    {P : Submodule A L} (Q : Submodule A L) {f : L} (hf : f ∈ P / P) : f ∈ (P * Q) / (P * Q) := by
  rw [Submodule.mem_div_iff_forall_mul_mem] at hf ⊢
  intro z hz
  refine Submodule.mul_induction_on hz (fun p hp q hq => ?_) (fun a b ha hb => ?_)
  · rw [← mul_assoc]
    exact Submodule.mul_mem_mul (hf p hp) hq
  · rw [mul_add]
    exact add_mem ha hb

theorem BlowUpColonFinite.proof (h₁ : PowSpanFinrankBounded.Statement.{u})
    (h₂ : PrincipalReductionOfBoundedGens.Statement.{u}) : BlowUpColonFinite.Statement.{u} := by
  intro A _ _ _ _ L _ _ hinj _hdim I hI
  obtain ⟨k, hk, y, hy, n₀, hred⟩ := h₂ A I (h₁ A _hdim I)
  have hlin : Algebra.linearMap A L = (Algebra.ofId A L).toLinearMap := LinearMap.ext fun _ => rfl
  have hmap : ∀ (J : Ideal A) (n : ℕ), (Submodule.map (Algebra.linearMap A L) J) ^ n =
      Submodule.map (Algebra.linearMap A L) (J ^ n) := fun J n => by
    rw [hlin]; exact (Submodule.map_pow _ _ n).symm
  set 𝓘 := Submodule.map (Algebra.linearMap A L) I with h𝓘

  have hy0 : y ≠ 0 := by
    rintro rfl
    have : I ^ (n₀ + k) = ⊥ := by
      rw [hred, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.bot_mul]
    exact pow_ne_zero _ hI this
  have hy' : algebraMap A L y ≠ 0 := fun h => hy0 (hinj (by rw [h, map_zero]))

  have hkey : ∀ s, 𝓘 ^ (n₀ + k * s) = Submodule.span A {algebraMap A L y ^ s} * 𝓘 ^ n₀ := by
    intro s
    rw [h𝓘, hmap, hmap, pow_add_mul_eq_span_pow_mul hred s, hlin, Submodule.map_mul,
      ← Ideal.submodule_span_eq, Submodule.map_span, Set.image_singleton,
      AlgHom.toLinearMap_apply, map_pow, Algebra.ofId_apply]

  have hle : ∀ n, 𝓘 ^ n / 𝓘 ^ n ≤ 𝓘 ^ n₀ / 𝓘 ^ n₀ := by
    intro n f hf
    have hn : n ≤ n₀ + k * n := by nlinarith
    have hf' := mem_div_self_mul_of_mem_div_self (𝓘 ^ (n₀ + k * n - n)) hf
    rw [← pow_add, Nat.add_sub_cancel' hn, hkey] at hf'
    rw [Submodule.mem_div_iff_forall_mul_mem] at hf' ⊢
    intro z hz
    obtain ⟨w, hw, hweq⟩ := Submodule.mem_span_singleton_mul.mp
      (hf' _ (Submodule.mem_span_singleton_mul.mpr ⟨z, hz, rfl⟩))
    have : f * z = w := by
      apply mul_left_cancel₀ (pow_ne_zero n hy')
      rw [hweq]; ring
    rw [this]; exact hw

  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  set c := algebraMap A L (a ^ n₀) with hc
  have hc0 : c ≠ 0 := fun h => pow_ne_zero n₀ ha0 (hinj (by rw [← hc, h, map_zero]))
  have hcI : c ∈ 𝓘 ^ n₀ := by
    rw [h𝓘, hmap]; exact Submodule.mem_map_of_mem (Ideal.pow_mem_pow haI n₀)
  have hfg : (𝓘 ^ n₀).FG := by
    rw [h𝓘, hmap]; exact (IsNoetherian.noetherian (I ^ n₀)).map _
  have hcol : (𝓘 ^ n₀ / 𝓘 ^ n₀).FG := by
    refine Submodule.fg_of_fg_map_injective (LinearMap.mulLeft A c)
      (fun x x' h => mul_left_cancel₀ hc0 h) (hfg.of_le ?_)
    rintro _ ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_div_iff_forall_mul_mem] at hf
    rw [LinearMap.mulLeft_apply, mul_comm]
    exact hf c hcI
  exact hcol.of_le (iSup_le hle)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocMax
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem subring_eq_of_isLocalization_atPrime {F : Type*} [Field F] {B R₁ R₂ : Subring F}
    (h₁ : B ≤ R₁) (h₂ : B ≤ R₂) (𝔭 : Ideal B) [𝔭.IsPrime]
    (hl₁ : letI := (Subring.inclusion h₁).toAlgebra; IsLocalization.AtPrime R₁ 𝔭)
    (hl₂ : letI := (Subring.inclusion h₂).toAlgebra; IsLocalization.AtPrime R₂ 𝔭) : R₁ = R₂ := by
  have key : ∀ (R₁ R₂ : Subring F) (h₁ : B ≤ R₁) (h₂ : B ≤ R₂),
      (letI := (Subring.inclusion h₁).toAlgebra; IsLocalization.AtPrime R₁ 𝔭) →
      (letI := (Subring.inclusion h₂).toAlgebra; IsLocalization.AtPrime R₂ 𝔭) → R₁ ≤ R₂ := by
    intro R₁ R₂ h₁ h₂ hl₁ hl₂ z hz
    let _ := (Subring.inclusion h₁).toAlgebra
    let _ := (Subring.inclusion h₂).toAlgebra
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔭.primeCompl (⟨z, hz⟩ : R₁)
    obtain ⟨t, ht⟩ := (IsLocalization.map_units R₂ s).exists_right_inv
    have e₁ : z * ((s : B) : F) = ((b : B) : F) := congrArg Subtype.val hbs
    have e₂ : ((s : B) : F) * (t : F) = 1 := congrArg Subtype.val ht
    have hzt : z = (b : F) * t := by
      calc z = z * (((s : B) : F) * t) := by rw [e₂, mul_one]
        _ = (z * ((s : B) : F)) * t := by ring
        _ = (b : F) * t := by rw [e₁]
    rw [hzt]
    exact R₂.mul_mem (h₂ b.2) t.2
  exact le_antisymm (key R₁ R₂ h₁ h₂ hl₁ hl₂) (key R₂ R₁ h₂ h₁ hl₂ hl₁)

theorem prime_eq_of_isLocalization_atPrime {F : Type*} [Field F] {B R : Subring F} (h : B ≤ R)
    (𝔭₁ 𝔭₂ : Ideal B) [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (hl₁ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₁)
    (hl₂ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₂) : 𝔭₁ = 𝔭₂ := by
  let _ := (Subring.inclusion h).toAlgebra
  have := hl₁
  have := hl₂
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R 𝔭₁
  rw [← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₁ inferInstance,
    ← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₂ inferInstance]

theorem BlowUpOverLocMax.proof (h₁ : BlowUpOverLocMaxPoint.Statement.{u})
    (h₂ : BlowUpOverLocPointMax.Statement.{u}) (h₃ : BlowUpLocRingInj.Statement.{u}) :
    BlowUpOverLocMax.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  have hpt := h₁ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have hmx := h₂ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  choose f hfT hfloc hfdeg using
    fun 𝔫 : {𝔫 : Ideal (blowUpOverLoc P W u) // 𝔫.IsMaximal} => hpt 𝔫.1 𝔫.2

  have hmh : ∀ W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes, IsMultiHomogIdeal W' :=
    fun W' hW' => MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W'
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'
  refine ⟨Equiv.ofBijective (fun 𝔫 => ⟨f 𝔫, hfT 𝔫⟩) ⟨?_, ?_⟩, fun 𝔫 => ⟨hfloc 𝔫, hfdeg 𝔫⟩⟩
  ·
    intro 𝔫₁ 𝔫₂ h12
    have hf : f 𝔫₁ = f 𝔫₂ := congrArg Subtype.val h12
    have hl₁ := hfloc 𝔫₁
    rw [hf] at hl₁
    obtain ⟨k₁, l₁⟩ := hl₁
    obtain ⟨k₂, l₂⟩ := hfloc 𝔫₂
    have := 𝔫₁.2.isPrime
    have := 𝔫₂.2.isPrime
    exact Subtype.ext (prime_eq_of_isLocalization_atPrime k₂ 𝔫₁.1 𝔫₂.1 l₁ l₂)
  ·
    rintro ⟨W', hW'⟩
    obtain ⟨k, 𝔫, h𝔫, hl⟩ := hmx W' hW'.1 hW'.2.1 hW'.2.2
    refine ⟨⟨𝔫, h𝔫⟩, Subtype.ext ?_⟩
    obtain ⟨k', hl'⟩ := hfloc ⟨𝔫, h𝔫⟩
    have := h𝔫.isPrime
    have hring : blowUpLocRing P u (f ⟨𝔫, h𝔫⟩) = blowUpLocRing P u W' :=
      subring_eq_of_isLocalization_atPrime k' k 𝔫 hl' hl
    have hT := hfT ⟨𝔫, h𝔫⟩
    exact h₃ O K ι J P u _ _ hT.1.1.1 (hmh _ hT.1) hT.2.1 (le_trans le_sup_left hT.1.1.2)
      hW'.1.1.1 (hmh _ hW'.1) hW'.2.1 (le_trans le_sup_left hW'.1.1.2) hring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

