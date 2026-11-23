module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import GroundTheory.LocalFields.Bundle0013
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0281
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeQuotientsNondegenerate

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumAddTwoMulDifferentExponentLe
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_add_two_mul_card_inf_le_of_not_le {G : Type} [Group G] [Finite G] (H J : Subgroup G)
    (h : ¬ H ≤ J) : Nat.card ↥H + 2 * Nat.card ↥(H ⊓ J) ≤ 2 * Nat.card ↥H := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (inf_le_left : H ⊓ J ≤ H)
  have hpos : 0 < Nat.card ↥(H ⊓ J) := Nat.card_pos
  have hposH : 0 < Nat.card ↥H := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply h
    have he := Subgroup.eq_of_le_of_card_ge (inf_le_left : H ⊓ J ≤ H) (by rw [hk, mul_one])
    rw [← he]
    exact inf_le_right
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 2 ≤ k := by omega
  rw [hk]
  nlinarith


open Classical in
theorem ite_add_two_mul_card_inf_sub_one_le {G : Type} [Group G] [Finite G] (H J : Subgroup G) :
    (if H ≤ J then 0 else Nat.card ↥H) + 2 * (Nat.card ↥(H ⊓ J) - 1) ≤ 2 * (Nat.card ↥H - 1) := by
  have h1 : 0 < Nat.card ↥(H ⊓ J) := Nat.card_pos
  have h2 : Nat.card ↥(H ⊓ J) ≤ Nat.card ↥H := Subgroup.card_le_of_le inf_le_left
  split_ifs with h
  · omega
  · have := card_add_two_mul_card_inf_le_of_not_le H J h
    omega

theorem jumpSum_add_two_mul_differentExponent_fixedField_le (F L : Type) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L]
    [IsGalois F L] (J : Subgroup (L ≃ₐ[F] L)) :
    jumpSum (wild F L) ⊤ J + 2 * differentExponent ↥(IntermediateField.fixedField J) L ≤
      2 * differentExponent F L := by
  classical
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot F L
  have hcard : ∀ i : ℤ, Nat.card ↥(lowerRamificationGroup (↥(IntermediateField.fixedField J)) L i) =
      Nat.card ↥(lowerRamificationGroup F L i ⊓ J) := by
    intro i
    rw [← lowerRamificationGroup_map_fixedField J i,
      Subgroup.card_map_of_injective (AlgEquiv.restrictScalarsHom_injective F)]
  have hFbot : lowerRamificationGroup F L ((N + 1 : ℕ) : ℤ) = ⊥ := hN _ (by push_cast; omega)
  have hMbot : lowerRamificationGroup (↥(IntermediateField.fixedField J)) L ((N + 1 : ℕ) : ℤ) = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ (AlgEquiv.restrictScalarsHom_injective F),
      lowerRamificationGroup_map_fixedField, hFbot, bot_inf_eq]
  have hjs : jumpSum (wild F L) ⊤ J = ∑ t ∈ Finset.range N,
      (if lowerRamificationGroup F L ((t + 1 : ℕ) : ℤ) ≤ J then 0
        else Nat.card ↥(lowerRamificationGroup F L ((t + 1 : ℕ) : ℤ))) := by
    unfold jumpSum
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N)]
    · refine Finset.sum_congr rfl fun t _ => ?_
      simp only [wild, top_inf_eq, Nat.cast_add, Nat.cast_one]
    · intro t ht
      rw [Function.mem_support] at ht
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h'
      apply ht
      simp only [wild, top_inf_eq]
      rw [hN _ (by omega)]
      simp
  rw [hjs, differentExponent_eq_sum_card_lowerRamificationGroup F L hFbot,
    differentExponent_eq_sum_card_lowerRamificationGroup _ L hMbot,
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [hcard]
  have hterm := Finset.sum_le_sum (s := Finset.range N) fun t _ =>
    ite_add_two_mul_card_inf_sub_one_le (lowerRamificationGroup F L ((t + 1 : ℕ) : ℤ)) J
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hterm
  have h0 : Nat.card ↥(lowerRamificationGroup F L ((0 : ℕ) : ℤ) ⊓ J) - 1 ≤
      Nat.card ↥(lowerRamificationGroup F L ((0 : ℕ) : ℤ)) - 1 :=
    Nat.sub_le_sub_right (Subgroup.card_le_of_le inf_le_left) 1
  rw [mul_add, mul_add]
  omega

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRange
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_eq_sum_range : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) (n : ℕ), Antitone R →
    (∀ t, t < n ↔ ¬ A ⊓ R t ≤ B) → jumpSum R A B = ∑ t ∈ Finset.range n, Nat.card ↥(A ⊓ R t) := by
  intro G _ R A B n _ h
  classical
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset (s := Finset.range n)]
  · refine Finset.sum_congr rfl fun t ht => ?_
    rw [if_neg ((h t).1 (Finset.mem_range.1 ht))]
  · intro t ht
    rw [Function.mem_support] at ht
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hn
    exact ht (if_pos (not_not.1 (mt (h t).2 hn)))

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumLeAdd
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

set_option backward.proofsInPublic true in
theorem jumpSum_support_subset {G : Type} [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) (hR : Antitone R)
    (m : ℕ) (hm : R m = ⊥) :
    Function.support (fun t : ℕ => by classical exact if A ⊓ R t ≤ B then 0 else Nat.card ↥(A ⊓ R t)) ⊆
      ↑(Finset.range m) := by
  classical
  intro t ht
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  push_neg at h
  apply ht
  have h1 : R t = ⊥ := le_bot_iff.mp (hm ▸ hR h)
  simp [h1]

theorem jumpSum_le_add : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R →
    (∃ m, R m = ⊥) → B ≤ A → jumpSum R A C ≤ jumpSum R A B + jumpSum R B C := by
  intro G _ R A B C hR ⟨m, hm⟩ hBA
  classical
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R A C hR m hm),
    finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R A B hR m hm),
    finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R B C hR m hm),
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  by_cases hC : A ⊓ R t ≤ C
  · simp [hC]
  · by_cases hB : A ⊓ R t ≤ B
    · have heq : B ⊓ R t = A ⊓ R t :=
        le_antisymm (inf_le_inf_right _ hBA) (le_inf hB inf_le_right)
      have hC' : ¬ B ⊓ R t ≤ C := by rw [heq]; exact hC
      simp [hC, hC', heq]
    · simp [hC, hB]

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumMonoOfLe
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram


open Classical in
theorem jumpSum_mono_of_le :
    ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R → (∃ m, R m = ⊥) →
      (∀ t, A ⊓ R t ≤ C → A ⊓ R t ≤ B) → jumpSum R A B ≤ jumpSum R A C := by
  intro G _ R A B C hR ⟨m, hm⟩ hBC
  have hbot : ∀ t, m ≤ t → ∀ D : Subgroup G, A ⊓ R t ≤ D := by
    intro t ht D
    have : R t ≤ ⊥ := hm ▸ hR ht
    exact le_trans inf_le_right (le_trans this bot_le)
  have hfin : ∀ D : Subgroup G,
      (Function.support fun t : ℕ => if A ⊓ R t ≤ D then 0 else Nat.card ↥(A ⊓ R t)) ⊆ ↑(Finset.range m) := by
    intro D
    intro t ht
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply ht
    simp [hbot t (not_lt.mp h) D]
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset _ (hfin B), finsum_eq_sum_of_support_subset _ (hfin C)]
  apply Finset.sum_le_sum
  intro t _
  by_cases hC : A ⊓ R t ≤ C
  · simp [hBC t hC]
  · rw [if_neg hC]
    split_ifs <;> simp

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.FracInv

theorem tied_frac_invariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (a b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, P.actQ g a * b = a * P.actQ g b) →
      ∃ c : ↥(K0 K), a = algebraMap ↥(K0 K) P.R.B c * b := by
  intro l _ P AI T K a b hb h
  have hF : IsField P.R.BdR := GlobalTheory.Per.FontaineBound.isField_of_tied T
  have h' : ∀ g, b * (P.PD K).actB g a = (P.PD K).actB g b * a := by
    intro g
    have := h g.1 g.2
    rw [P.PD_actB, P.PD_actB, mul_comm, this, mul_comm]
  obtain ⟨c, hc⟩ := GlobalTheory.Per.FontaineBound.frac_dR (P.PD K) hF ((P.PD K).ι b) ((P.PD K).ι a)
    (fun h0 => hb ((P.PD K).ι_inj (h0.trans (map_zero _).symm)))
    (fun g => by rw [← (P.PD K).ι_comm, ← (P.PD K).ι_comm, ← map_mul, ← map_mul, h' g])
  have hcU : (c : Om l) ∈ MaximalUnramifiedExtension l := by
    refine GlobalTheory.FracAlg.mem_Kur_of_ratio l P AI T a b (c : Om l) hb ?_
    have h1 := hc
    rw [P.PD_ι, P.PD_ι] at h1
    exact h1
  refine ⟨⟨c, c.2, hcU⟩, (P.PD K).ι_inj ?_⟩
  rw [map_mul, AlgHom.commutes, hc]
  rfl

end GlobalTheory.Per.FracInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormEqSumLocalisationProjections
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.NSideDecomp

theorem part_le_off' {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [IsLocalRing O] (T : Subalgebra O (Module.End K V)) {I J : Ideal T}
    (h : I ≠ J) : NCov.part T I ≤ NCov.off T J :=
  iSup₂_le fun ψ hψ => le_iSup₂_of_le (f := fun ψ (_ : NCov.cls ψ ≠ J) => NCov.W T (NCov.pt ψ)) ψ
    (by rw [hψ]; exact h) le_rfl

theorem iV_eq_sum_Psi : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → ∀ y : D.what₂.MtL (D.what₂.muTw w) j, T.B.iV j w y = ∑ i ∈ (D.nd.locs j w).attach, T.Psi j w i.1 i.2 (D.nd.prMt i.1 (castMtInv D i.2 y)) := by
  classical
  intro D M T j w h1 h2 hw hstd y
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, hsplit, hint⟩ := gens_hypsTw T.B hstd h1 h2 (Or.inl hw)
  have hinj := IsFractionRing.injective (T.B.Oc j w) (FractionRing (T.B.Oc j w))
  rw [← sub_eq_zero]
  refine NCov.eq_zero_of_forall_mem_off hinj hS hsplit hint ((D.nd.locs j w).image (T.mx j w))
    (fun I hI => ?_) ?_
  · obtain ⟨i, hi, rfl⟩ := T.mx_all j w h1 h2 hw I hI
    exact Finset.mem_image_of_mem _ hi
  · intro I hI
    obtain ⟨i0, hi0, rfl⟩ := Finset.mem_image.1 hI
    rw [← Finset.add_sum_erase _ _ (Finset.mem_attach _ ⟨i0, hi0⟩), sub_add_eq_sub_sub]
    refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun i hi => ?_)
    · have e := T.Psi_pr j w i0 hi0 (castMtInv D hi0 y)
      rw [castMt_castMtInv] at e
      rw [← neg_sub]
      exact Submodule.neg_mem _ e
    · have hne : T.mx j w i.1 ≠ T.mx j w i0 := by
        intro e
        have := T.mx_inj j w i.2 hi0 e
        exact (Finset.mem_erase.1 hi).1 (Subtype.ext this)
      exact part_le_off' _ hne ((T.Psi_range j w i.1 i.2 _).2 ⟨_, rfl⟩)

end GlobalTheory.NSideDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBoundOfBoundOnSets
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys

namespace GlobalTheory.TwSys.ResidualCompare

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem isConjPl_unique {P v v' : PlE D.host} (h : IsConjPl D.host P v) (h' : IsConjPl D.host P v') : v = v' := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, hx⟩ := (RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv).surjective y
  have hy : (y : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [← hx]; rfl
  rw [← h x y hy, ← h' x y hy]

variable (bkP : BKPh X)

end GlobalTheory.TwSys.ResidualCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueIndepOfNotReducibleOverUnramified
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResIndep

variable {l : ℕ} [Fact l.Prime]

theorem fr_bijective (l : ℕ) [Fact l.Prime] (m : ℕ) : Function.Bijective (fr l m) := by
  have e : (fr l m : ↥(MaximalUnramifiedExtension l) → ↥(MaximalUnramifiedExtension l)) = (frobUr l)^[m] := by
    funext c
    simp [fr, AlgHom.coe_pow]
  rw [e]
  exact frobUr_bijective.iterate m

variable (P : LocPrime l) {n : Type} [Fintype n] [DecidableEq n]

def resS (m : ℕ) (u : n → P.R.BdR) (d : n → ↥(MaximalUnramifiedExtension l)) : P.R.BdR := ∑ i, kd P (fr l m (d i)) * u i

theorem resS_zero (m : ℕ) (u : n → P.R.BdR) : resS P m u 0 = 0 := by simp [resS]

theorem resS_add (m : ℕ) (u : n → P.R.BdR) (d e : n → ↥(MaximalUnramifiedExtension l)) :
    resS P m u (d + e) = resS P m u d + resS P m u e := by
  simp [resS, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem resS_neg (m : ℕ) (u : n → P.R.BdR) (d : n → ↥(MaximalUnramifiedExtension l)) : resS P m u (-d) = -resS P m u d := by
  simp [resS, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem resS_smul (m : ℕ) (u : n → P.R.BdR) (e : ↥(MaximalUnramifiedExtension l)) (d : n → ↥(MaximalUnramifiedExtension l)) :
    resS P m u (e • d) = kd P (fr l m e) * resS P m u d := by
  simp [resS, Finset.mul_sum, mul_assoc]

def resW (r m : ℕ) (u : n → P.R.BdR) : AddSubgroup (n → ↥(MaximalUnramifiedExtension l)) where
  carrier := {d | (∀ i, fr l r (d i) = d i) ∧ resS P m u d ∈ Fil P 1}
  zero_mem' := ⟨fun i => by simp, by rw [resS_zero]; exact Fil_zero_mem 1⟩
  add_mem' := fun {x y} hx hy => ⟨fun i => by simp [hx.1 i, hy.1 i], by rw [resS_add]; exact Fil_add hx.2 hy.2⟩
  neg_mem' := fun {x} hx => ⟨fun i => by simp [hx.1 i], by rw [resS_neg]; exact Fil_neg hx.2⟩

theorem rat_vecMul {K : FinExt l} {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (hR : IsRat r ρ) (d : n → ↥(MaximalUnramifiedExtension l))
    (hd : ∀ i, fr l r (d i) = d i) (g : ↥(GK K)) (j : n) :
    fr l r (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j) = Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j := by
  change fr l r (∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = ∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hd, hR.rat]

theorem key {K : FinExt l} {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (hR : IsRat r ρ) (m : ℕ) (u : n → P.R.BdR) (a : ℤ)
    (g : ↥(GK K))
    (hrel : (matD P ρ m g).mulVec (fun i => P.actQdR (g : GQ l) (u i)) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a : ℚ_[l]ˣ) : ℚ_[l]) • u)
    (d : n → ↥(MaximalUnramifiedExtension l)) (hd : ∀ i, fr l r (d i) = d i)
    (h : resS P m u (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l))) ∈ Fil P 1) : resS P m u d ∈ Fil P 1 := by
  set q : ℚ_[l]ˣ := P.χQ (g : GQ l) ^ a with hq
  have hi : ∀ i, algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * u i =
      ∑ j, kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j) := by
    intro i
    have := congrFun hrel i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, matD, Matrix.map_apply] at this
    exact this.symm
  have hfix : ∀ j, P.actQdR (g : GQ l) (kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j))) =
      kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j)) := fun j =>
    act_kd P g (hR.le _ (fr_comm (rat_vecMul hR d hd g j) m))
  have e1 : algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * resS P m u d =
      P.actQdR (g : GQ l) (resS P m u (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)))) := by
    have hR' : ∀ j, P.actQdR (g : GQ l) (kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j)) * u j) =
        ∑ i, kd P (fr l m (d i)) * (kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j)) := by
      intro j
      rw [map_mul, hfix j]
      change kd P (fr l m (∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * _ = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, mul_assoc]
    have hL : ∀ i, algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * (kd P (fr l m (d i)) * u i) =
        ∑ j, kd P (fr l m (d i)) * (kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j)) := by
      intro i
      rw [mul_left_comm, hi i, Finset.mul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [resS, resS, map_sum, Finset.mul_sum]
    simp_rw [hR', hL]
    exact Finset.sum_comm
  have h1 : algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * resS P m u d ∈ Fil P 1 := e1 ▸ Fil_act (g : GQ l) h
  have h2 := Fil_mul_left (q_mem_Fil P ((q⁻¹ : ℚ_[l]ˣ) : ℚ_[l])) h1
  rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at h2

end GlobalTheory.PMon.ResIndep

namespace GlobalTheory.PMon


open GlobalTheory.PMon.ResIndep in
theorem residue_indep_of_not_splits : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (u : n → P.R.BdR) (a : ℤ), IsRat r ρ → ¬ Splits r ρ → (∀ i, u i ∈ Fil P 0) → (∃ i, u i ∉ Fil P 1) → (∀ g : ↥(GK K), (matD P ρ m g).mulVec (fun i => P.actQdR (g : GQ l) (u i)) = algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a : ℚ_[l]ˣ) : ℚ_[l]) • u) → ∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * u i ∈ Fil P 1 → c = 0 := by
  intro l _ P AI T n _ _ K r ρ m u a hR hNS _ hu1 hrel c hc hS
  by_contra hc0
  apply hNS
  have hbij := fr_bijective l m
  refine _root_.GlobalTheory.PMon.splits_of_stable_rat_subspace l n K r ρ hR (resW P r m u) (fun d hd => hd.1) ?_ ?_ ?_ ?_
  · intro e he d hd
    refine ⟨fun i => ?_, ?_⟩
    · simp [Pi.smul_apply, smul_eq_mul, map_mul, he, hd.1 i]
    · rw [resS_smul]
      exact Fil_mul_left (kd_mem_Fil P _) hd.2
  · intro g d hd
    have hd1 : ∀ i, fr l r (d i) = d i := hd.1
    have hd' : ∀ j, fr l r (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j) = Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j :=
      rat_vecMul hR d hd1 g
    refine ⟨hd', key P hR m u a g⁻¹ (hrel g⁻¹) _ hd' ?_⟩
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.vecMul_one]
    exact hd.2
  · choose d hd using fun i => hbij.2 (c i)
    have hdr : ∀ i, fr l r (d i) = d i := fun i => hbij.1 (by
      rw [← fr_add, add_comm, fr_add, hd i, hc i])
    intro hbot
    have hmem : d ∈ resW P r m u := ⟨hdr, by
      change ∑ i, kd P (fr l m (d i)) * u i ∈ Fil P 1
      simpa only [hd] using hS⟩
    rw [hbot, AddSubgroup.mem_bot] at hmem
    apply hc0
    funext i
    rw [← hd i, hmem]
    simp
  · obtain ⟨i0, hi0⟩ := hu1
    refine ⟨Pi.single i0 1, fun i => ?_, fun hmem => hi0 ?_⟩
    · by_cases h : i = i0
      · subst h; simp
      · simp [h]
    · have e : resS P m u (Pi.single i0 1) = u i0 := by
        simp [resS, Pi.single_apply]
      rw [← e]
      exact hmem.2

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatumStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_H2_period_datum : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), LocalTateTopDegree (P.PD K) := by
  first | exact @GlobalTheory.TateTop.tateH2_of_duality_loc | exact GlobalTheory.TateTop.tateH2_of_duality_loc | (intros; apply GlobalTheory.TateTop.tateH2_of_duality_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeQuotientsNondegenerateStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_pairing_lattice_quotients_nondegenerate : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), (∀ c ∈ quotientCocycles LA _ hI, (∀ c' ∈ quotientCocycles LA' _ hI', CobO (P.PD K) L1 (fun x => (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' x.2))))) → c ∈ BQ LA _ hI) ∧ (∀ c' ∈ quotientCocycles LA' _ hI', (∀ c ∈ quotientCocycles LA _ hI, CobO (P.PD K) L1 (fun x => (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' x.2))))) → c' ∈ BQ LA' _ hI') := by
  first | exact @GlobalTheory.TateFin.tate_pairing_nondegenerate | exact GlobalTheory.TateFin.tate_pairing_nondegenerate | (intros; apply GlobalTheory.TateFin.tate_pairing_nondegenerate <;> assumption)
end

