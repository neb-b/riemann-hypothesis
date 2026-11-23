module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeTieCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.FWT
  Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Local

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

variable {WL : ℕ → Type} [∀ j, AddCommGroup (WL j)] [∀ j, Module D.what₂.LL (WL j)]
  (e : ∀ i : Fin D.R.m, WL ((i : ℕ) + 1) ≃ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL))

theorem isSplitPl_iff (P : PlE D.host) :
    IsSplitPl D.host P ↔ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal := by
  have hc : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (GlobalTheory.SplitOffPlaces.conjSpec P).asIdeal := by
    rw [Formalism.L2.Col.conjIdeal_eq]; rfl
  rw [hc]
  constructor
  · rintro ⟨x, hx, h⟩ he
    refine h (Formalism.L2.Col.cO D.host.E x) (bridge_star_holds D.R D.host _) ?_
    rw [← he] at hx
    exact hx
  · intro hne
    by_contra h
    refine hne (P.isMaximal.eq_of_le (GlobalTheory.SplitOffPlaces.conjSpec P).isPrime.ne_top fun x hx => ?_).symm
    by_contra hx'
    refine h ⟨x, hx, fun y hy hyP => hx' ?_⟩
    have : y = Formalism.L2.Col.cO D.host.E x := RingOfIntegers.ext (hy.trans (bridge_star_holds D.R D.host _).symm)
    rw [this] at hyP
    exact hyP

theorem level_notMem {P : PlE D.host} (h : ∃ i', P ∉ D.ntw.S0 i') :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨i', hi⟩ := h
  intro hm
  rw [Nat.cast_mul] at hm
  rcases P.isPrime.mem_or_mem hm with h | h
  · exact hi (D.ntw.placesOver_subset_exceptional i' 0 h)
  · exact hi (D.ntw.placesOver_subset_exceptional i' 1 h)

theorem scalar_eq (i : Fin D.R.m) (P : PlE D.host) (k : ℕ) :
    (((R.C.mu0 i).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹ = heckeScalar R i P k := by
  rw [heckeScalar, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_pow]

theorem exists_family (t : ∀ i : Fin D.R.m, ℕ → PlE D.host → Module.End D.what₂.LL (Fin (R.nW i) → D.what₂.LL)) :
    ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (WL j),
      ∀ (i : Fin D.R.m) k P, (e i).conj (hL ((i : ℕ) + 1) k P) = t i k P := by
  refine ⟨fun j => match j with
    | 0 => fun _ _ => 0
    | n + 1 => fun k P => if h : n < D.R.m then (e ⟨n, h⟩).symm.conj (t ⟨n, h⟩ k P) else 0, fun i k P => ?_⟩
  simp only [dif_pos i.2]
  exact (e i).conj.apply_symm_apply (t i k P)

end Local

section Comparison₂

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  {WL : ℕ → Type} [∀ j, AddCommGroup (WL j)] [∀ j, Module D.what₂.LL (WL j)]
  (e : ∀ i : Fin D.R.m, WL ((i : ℕ) + 1) ≃ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL))

end Comparison₂

end GlobalTheory.HeckeTieCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedModelSelfDualLatticeInvariantLinearFo
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ} {n n' : ℕ}

theorem mem_mixLat_iff {x : Matrix (Fin n') (Fin n) L} : x ∈ mixLat L n' n ↔ ∀ r c,
    (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2 → x r c = 0) ∧ (n' / 2 ≤ r.1 → c.1 < n - n / 2 → x r c ∈ intL L) :=
  Iff.rfl

theorem pairing_mixLat (hσ : ∀ x, σ (σ x) = x) (hv : ∀ x, Valued.v (σ x) = Valued.v x) (hδ : Valued.v δ = 1)
    (hψ0 : ∀ a ∈ intL L, σ a = a → ψ a = 1) {a b : Matrix (Fin n') (Fin n) L} (ha : a ∈ mixLat L n' n)
    (hb : b ∈ mixLat L n' n) : pairing σ δ ψ a b = 1 := by
  have hs : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => mem_intL.2 ((hv x).trans_le hx)
  rw [mem_mixLat_iff] at ha hb
  have hS : ∑ i, ∑ j, a i j * σ (b i.rev j.rev) ∈ intL L := by
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    have hai := ha i j
    have hbi := hb i.rev j.rev
    simp only [Fin.val_rev] at hbi
    have := i.isLt
    have := j.isLt
    by_cases h1 : n' - n' / 2 ≤ i.1 ∨ n' / 2 ≤ i.1 ∧ j.1 < n / 2
    · rw [hai.1 h1, zero_mul]; exact zero_mem _
    by_cases h2 : n' - n' / 2 ≤ n' - (i.1 + 1) ∨ n' / 2 ≤ n' - (i.1 + 1) ∧ n - (j.1 + 1) < n / 2
    · rw [hbi.1 h2, map_zero, mul_zero]; exact zero_mem _
    exact mul_mem (hai.2 (by omega) (by omega)) (hs _ (hbi.2 (by omega) (by omega)))
  have hi : δ * ∑ i, ∑ j, a i j * σ (b i.rev j.rev) ∈ intL L := mul_mem (mem_intL.2 hδ.le) hS
  exact hψ0 _ (add_mem hi (hs _ hi)) (by rw [map_add (f := _), hσ, add_comm])

theorem exists_bad_entry (x : Matrix (Fin n') (Fin n) L)
    (hx : ¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) :
    ∃ r c, x r c ∉ intL L ∧ (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2) := by
  by_contra hc
  refine hx ⟨fun r c => if n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2 then 0 else x r c, fun r c =>
    ⟨fun e => by dsimp only; rw [if_pos (by omega)], fun e e' => by dsimp only; rw [if_pos (by omega)]; exact zero_mem _⟩,
    fun r c => ?_⟩
  show x r c - (if n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2 then 0 else x r c) ∈ intL L
  split_ifs with hb
  · rw [sub_zero]
    by_contra hi
    exact hc ⟨r, c, hi, hb⟩
  · rw [sub_self]; exact zero_mem _

variable {M : Type} [AddCommGroup M] [Module ℂ M]
variable {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M} {ω : GU σ n × GU σ n' →* Module.End ℂ M} {s : M}

theorem IsStd.form_eq_zero (h : IsStd ϖ σ q δ ψ ρ ω s) (ℓ' : M →ₗ[ℂ] ℂ)
    (hℓ' : ∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) (x : Matrix (Fin n') (Fin n) L) (r : Fin n') (c : Fin n)
    (hx : x r c ∉ intL L) (hrc : n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2) : ℓ' (ρ x s) = 0 := by
  obtain ⟨u, hu, hne⟩ := exists_pairing_single_ne h.1.unr h.v_two h.1.delta.1 h.1.psi_ne x hx
  have := r.isLt
  have := c.isLt
  have hyA : Matrix.single r.rev c.rev u ∈ mixLat L n' n := by
    intro r' c'
    rw [Matrix.single_apply]
    split_ifs with he
    · obtain ⟨rfl, rfl⟩ := he
      simp only [Fin.val_rev]
      exact ⟨fun e => by omega, fun _ _ => hu⟩
    · exact ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  have hyL : Matrix.single r.rev c.rev u ∈ intMat L (Fin n') (Fin n) := by
    intro i j
    rw [Matrix.single_apply]
    split_ifs
    exacts [hu, zero_mem _]
  have e1 := h.isHeis.comm x (Matrix.single r.rev c.rev u) s
  rw [h.fixes _ hyL] at e1
  have e2 := congrArg ℓ' e1
  rw [map_smul, hℓ' _ hyA, smul_eq_mul] at e2
  have e3 : (pairing σ δ ψ x (Matrix.single r.rev c.rev u) - 1) * ℓ' (ρ x s) = 0 := by linear_combination -e2
  rcases mul_eq_zero.1 e3 with h' | h'
  · exact absurd (sub_eq_zero.1 h') hne
  · exact h'

end

theorem exists_mixLat_form : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) ∧ (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) ∧ (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ℓ (ρ (embLow n' n z) s) = if z ∈ intMat L (Fin (n' / 2)) (Fin (n / 2)) then 1 else 0 := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s h
  obtain ⟨ℓ, h1, h2⟩ := _root_.GlobalTheory.SphTheta.exists_linearForm_invariant_isotropic_vacuum h.isHeis (intMat L (Fin n') (Fin n)) h.selfDual s h.2.1 h.fixes h.2.2.2
    (mixLat L n' n) fun a ha b hb => pairing_mixLat h.1.unr.1 h.1.unr.2.1 h.1.delta.1 h.1.psi_int ha hb
  have hz : ∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ x,
      (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ' (ρ x s) = 0 := fun ℓ' hℓ' x hx => by
    obtain ⟨r, c, hr, hrc⟩ := exists_bad_entry x hx
    exact h.form_eq_zero ℓ' hℓ' x r c hr hrc
  refine ⟨ℓ, h1, h2, hz ℓ h2, fun ℓ' hℓ' => ?_, fun z => ?_⟩
  · have key : ℓ' = ℓ' s • ℓ := LinearMap.ext_on_range h.2.2.2 fun x => ?_
    · exact fun v => LinearMap.congr_fun key v
    show ℓ' (ρ x s) = (ℓ' s • ℓ) (ρ x s)
    by_cases hx : ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)
    · obtain ⟨a, ha, hxa⟩ := hx
      have e := h.isHeis.comp a (x - a) s
      rw [h.fixes _ hxa, show a + (x - a) = x by abel] at e
      have hg := h.isHeis.ne_zero (half h.v_two • a) (x - a)
      have hx' : ρ x s = (pairing σ δ ψ (half h.v_two • a) (x - a))⁻¹ • ρ a s := by
        rw [e, smul_smul, inv_mul_cancel₀ hg, one_smul]
      rw [LinearMap.smul_apply, hx', map_smul, map_smul, hℓ' a ha, h2 a ha, h1, smul_eq_mul, smul_eq_mul, smul_eq_mul,
        mul_one, mul_comm]
    · rw [LinearMap.smul_apply, hz ℓ' hℓ' x hx, hz ℓ h2 x hx, smul_zero]
  · have := (n' / 2).le_refl
    split_ifs with hzi
    · have hm : embLow n' n z ∈ intMat L (Fin n') (Fin n) := fun r c => by
        unfold embLow
        split_ifs
        exacts [hzi _ _, zero_mem _]
      rw [h.fixes _ hm, h1]
    · obtain ⟨i, j, hij⟩ : ∃ i j, z i j ∉ intL L := by
        by_contra hc
        push_neg at hc
        exact hzi hc
      have he : embLow n' n z (hi n' i) (hi n j) = z i j := by
        simp [embLow, hi]
      refine h.form_eq_zero ℓ h2 _ (hi n' i) (hi n j) (by rwa [he]) (Or.inl ?_)
      simp only [hi]
      omega

end GlobalTheory.SphTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpOfTranslates
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeClassSums

section Linear

variable {L : Type} [Field L] {σ : L →+* ℂ} {H : Type} [AddCommGroup H] [Module ℂ H]

end Linear

section Group

open Formalism.IndefR.Bridge

variable {G : Type} [Group G]

end Group

section Row

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
  Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Local

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

variable {R}


set_option maxHeartbeats 1000000 in
theorem span_jV (hV : R.models_HV) (hj : R.models_jV) (i : Fin D.R.m) (t : T0) : Submodule.span ℂ (Set.range (R.jV i t)) = ⊤ := by
  apply Submodule.map_injective_of_injective (hV i t).1
  rw [Submodule.map_span, Submodule.map_top, (hV i t).2.1, ← Set.range_comp]
  have h1 : (⇑(R.HV i t).e ∘ ⇑(R.jV i t)) = ⇑((R.B.L i t).pres.extL) := funext fun x => hj i t x
  rw [h1]
  exact GlobalTheory.PresBasic.ext_span (R.B.L i t).pres

end Local

section Comparison₂

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

end Comparison₂

end Row

end GlobalTheory.HeckeClassSums
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAction

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem conj_mem_flag1 {g0 : G0 L.Pg L.r} {κ k : GA D V} (hκ : IsLevelLift V β L g0 κ)
    (hk : k ∈ levG V β (flag1L L)) :
    κ⁻¹ * (k * κ) ∈ levG V β (flag1L L) ∧
      levChi V β (flag1L L) (κ⁻¹ * (k * κ)) = levChi V β (flag1L L) k := by
  obtain ⟨hκf, hκp, hκr⟩ := hκ
  rw [levG, mem_levA, Formalism.L2.DIV.mem_lev] at hk
  obtain ⟨hkf, hkp, hkr⟩ := hk

  have hxp : finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := hkp
  have hx1 : Formalism.L2.DIV.rTup β L (finE V k) = 1 := Subgroup.mem_bot.mp hkr
  have hfin : finE V (κ⁻¹ * (k * κ)) = (finE V κ)⁻¹ * (finE V k * finE V κ) := by
    rw [map_mul, map_mul, map_inv]
  have hcp : (finE V κ)⁻¹ * (finE V k * finE V κ) ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hκp) (Subgroup.mul_mem _ hxp hκp)
  refine ⟨?_, ?_⟩
  · rw [levG, mem_levA, Formalism.L2.DIV.mem_lev, hfin]
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hκf) (Subgroup.mul_mem _ hkf hκf), hcp, ?_⟩
    have hr : Formalism.L2.DIV.rTup β L ((finE V κ)⁻¹ * (finE V k * finE V κ)) = 1 := by
      rw [Formalism.L2.DIV.rTup_mul (Subgroup.inv_mem _ hκp) (Subgroup.mul_mem _ hxp hκp),
        Formalism.L2.DIV.rTup_inv hκp, Formalism.L2.DIV.rTup_mul hxp hκp, hx1, one_mul, inv_mul_cancel]
    exact Subgroup.mem_bot.mpr hr
  ·
    show ((Formalism.L2.DIV.levFn β (flag1L L) (finE V (κ⁻¹ * (k * κ))) : ℂˣ) : ℂ) =
      ((Formalism.L2.DIV.levFn β (flag1L L) (finE V k) : ℂˣ) : ℂ)
    rw [levFn_flag1, levFn_flag1, hfin]
    have hA : finE V κ ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) :=
      Formalism.L2.DIV.mem_lev.mpr ⟨hκp, Subgroup.mem_top _⟩
    have hX : finE V k ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) :=
      Formalism.L2.DIV.mem_lev.mpr ⟨hxp, Subgroup.mem_top _⟩
    let A : Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) := ⟨finE V κ, hA⟩
    let X : Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) := ⟨finE V k, hX⟩
    have hc : Formalism.L2.DIV.levChar D.sp.cm V.gram β (flagL L) (A⁻¹ * (X * A)) =
        Formalism.L2.DIV.levChar D.sp.cm V.gram β (flagL L) X := by
      rw [map_mul, map_mul, map_inv]
      exact inv_mul_cancel_comm_assoc _ _
    have e1 := Formalism.L2.DIV.levChar_apply (A⁻¹ * (X * A))
    have e2 := Formalism.L2.DIV.levChar_apply X
    exact congrArg (fun u : ℂˣ => (u : ℂ)) (e1.symm.trans (hc.trans e2))

theorem finiteGroupAction_preserves_principalFlagMultiplicity : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), IsInfFam θ → ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (g0 : G0 L.Pg L.r), ∀ T ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)), ∀ U : MMap M, (∀ v, U v = actG0 V β L g0 (T v)) → U ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
  intro D V S θ M _ β L g0 T hT U hU
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
  ·
    have hκ : IsLevelLift V β L g0 hk.choose := hk.choose_spec
    have hEq : U = (levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T := by
      ext v h
      rw [hU v, MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      unfold actG0
      rw [dite_eq_left hk]
      congr 1
      show T v (h * hk.choose) = ∑ γ ∈ ({hk.choose} : Finset (GA D V)), T v (h * γ)
      rw [Finset.sum_singleton]
    rw [hEq]
    refine GlobalTheory.MultMem.isMultMap_smul _ (GlobalTheory.SphericalOps.isMultMap_heckeOn hT ?_ ?_)
    · intro k hk'
      rw [Finset.mem_singleton.mp hk']
      exact hκ.1
    · intro v k hkJ g
      show ∑ γ ∈ ({hk.choose} : Finset (GA D V)), T v (g * k * γ) =
        levChi V β (flag1L L) k * ∑ γ ∈ ({hk.choose} : Finset (GA D V)), T v (g * γ)
      rw [Finset.sum_singleton, Finset.sum_singleton]
      obtain ⟨hmem, hchi⟩ := conj_mem_flag1 hκ hkJ
      have hl := hT.lev v _ hmem (g * hk.choose)
      rw [hchi] at hl
      rw [← hl]
      congr 1
      simp [mul_assoc]
  ·
    have hEq : U = 0 := by
      ext v h
      rw [hU v]
      unfold actG0
      rw [dite_eq_right hk]
      rfl
    rw [hEq]
    exact GlobalTheory.MultMem.isMultMap_zero

end GlobalTheory.FlagAction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
section
noncomputable section

namespace GlobalTheory.FockFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def blockB (J : (V × V) →ₗ[ℝ] (V × V)) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (LinearMap.fst ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V)

def blockD (J : (V × V) →ₗ[ℝ] (V × V)) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (LinearMap.snd ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V)

theorem blockB_apply (J : (V × V) →ₗ[ℝ] (V × V)) (q : V) : blockB J q = (J (0, q)).1 := rfl

theorem blockD_apply (J : (V × V) →ₗ[ℝ] (V × V)) (q : V) : blockD J q = (J (0, q)).2 := rfl

def fockForm (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) : V →ₗ[ℝ] V →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ
    (fun x y => ((Real.pi * β x (Ring.inverse (blockB J) y) : ℝ) : ℂ) +
      (Real.pi : ℂ) * Complex.I * ((β x (blockD J (Ring.inverse (blockB J) y)) : ℝ) : ℂ))
    (fun x x' y => by simp only [map_add (f := _), LinearMap.add_apply]; push_cast; ring)
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.real_smul]; push_cast; ring)
    (fun x y y' => by simp only [map_add (f := _)]; push_cast; ring)
    (fun c x y => by simp only [map_smul, smul_eq_mul, Complex.real_smul]; push_cast; ring)

theorem fockForm_apply (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (x y : V) :
    fockForm β J x y = ((Real.pi * β x (Ring.inverse (blockB J) y) : ℝ) : ℂ) +
      (Real.pi : ℂ) * Complex.I * ((β x (blockD J (Ring.inverse (blockB J) y)) : ℝ) : ℂ) := rfl

end GlobalTheory.FockFamily

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReductions
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRed

theorem frMapO_actO_int_red : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP : Pl D.host.E, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) :=
  frMapO_actO_red

end GlobalTheory.FrameRed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumUniqueOfSelfDualStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergVacuum_unique_of_selfDual : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ v, Fixes W Λ v → ∃ c : ℂ, v = c • s := by
  first | exact @GlobalTheory.SphTheta.vacuum_unique_of_selfDual | exact GlobalTheory.SphTheta.vacuum_unique_of_selfDual | (intros; apply GlobalTheory.SphTheta.vacuum_unique_of_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjectiveStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetModule_map_injective_of_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL n k) V) (π : Representation ℂ (GL n k) W) (f : π₁.IntertwiningMap π), IsSmooth π → Function.Injective f → Function.Injective (jacMap e f) := by
  first | exact @GlobalTheory.JacInj.jacMap_injective | exact GlobalTheory.JacInj.jacMap_injective | (intros; apply GlobalTheory.JacInj.jacMap_injective <;> assumption)
end

