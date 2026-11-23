module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0038
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsXPowSmulEqPrimePowSmulPhiModule
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilRingModHighDegreeProperty
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]

theorem wS_eq_one_of_lt (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] {e n : ℕ}
    (hn : n < l * e) : wS K e n = 1 := by
  have hp : l.Prime := Fact.out
  have h1 : n / e < l := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simpa using hp.pos
    · exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hn)
  have hc : Nat.Coprime l (n / e).factorial :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => absurd (hp.dvd_factorial.1 h) (by omega)
  unfold wS
  rw [norm_natCast_eq l, Padic.norm_natCast_eq_one_iff]
  first | exact hc | exact hc.symm

theorem norm_coeff_N_mul_wS_le (e : ℕ) (f : K⟦X⟧) (n : ℕ) :
    ‖coeff n (N K f)‖ * wS K e n ≤ ‖coeff n f‖ * wS K e n := by
  rw [coeff_N, norm_mul, mul_assoc]
  exact mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (wS_nonneg _ _))
    (IsUltrametricDist.norm_natCast_le_one K n)

theorem N_mem_S {e : ℕ} {f : K⟦X⟧} (hf : f ∈ S O K e) : N K f ∈ S O K e :=
  ⟨fun n => (norm_coeff_N_mul_wS_le e f n).trans (hf.1 n),
    squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n))
      (norm_coeff_N_mul_wS_le e f) hf.2⟩

theorem ringModHigh : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a], GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.RingModHigh O K l e := by
  intro O K _ _ _ _ _ _ l e a _ _ _ _
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    refine ⟨⟨N K (f : K⟦X⟧), N_mem_S f.2⟩, ?_, rfl⟩
    refine GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_SHigh.2 (X_pow_dvd_iff.2 fun m hm => ?_)
    change coeff m (N K (f : K⟦X⟧)) = 0
    rw [coeff_N, X_pow_dvd_iff.1 (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_SHigh.1 hf) m hm, mul_zero]
  · intro f
    constructor
    · intro hf
      set g : K⟦X⟧ := ((trunc (l * e) f : Polynomial K) : K⟦X⟧) with hgdef
      have hg : ∀ n, coeff n g = if n < l * e then coeff n f else 0 := by
        intro n
        rw [hgdef, Polynomial.coeff_coe, coeff_trunc]
      have gA : g ∈ A O K := fun n => by
        rw [hg]
        split_ifs with h
        · have := hf.1 n
          rwa [wS_eq_one_of_lt l h, mul_one] at this
        · simp
      refine ⟨g, gA, ⟨f - g, (S O K e).sub_mem hf (A_le_S l e gA)⟩,
        GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_SHigh.2 (X_pow_dvd_iff.2 fun m hm => ?_), by simp⟩
      change coeff m (f - g) = 0
      rw [map_sub, hg, if_pos hm, sub_self]
    · rintro ⟨g, hg, h, -, rfl⟩
      exact (S O K e).add_mem (A_le_S l e hg) h.2
  · intro f
    constructor
    · rintro ⟨hfA, h, hh, rfl⟩
      obtain ⟨g, hg⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_SHigh.1 hh
      refine ⟨g, fun n => ?_, by rw [hg, ← pow_mul, mul_comm e l]⟩
      have := hfA (n + l * e)
      rwa [hg, coeff_X_pow_mul] at this
    · rintro ⟨g, hg, rfl⟩
      have hm : ((X : K⟦X⟧) ^ e) ^ l * g ∈ A O K :=
        (A O K).mul_mem ((A O K).pow_mem ((A O K).pow_mem HasU.X_mem e) l) hg
      exact ⟨hm, ⟨_, A_le_S l e hm⟩,
        GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_SHigh.2 ⟨g, by
          change ((X : K⟦X⟧) ^ e) ^ l * g = _
          rw [← pow_mul, mul_comm e l]⟩, rfl⟩

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColonIdealFrobeniusLeMapExpand
section
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

noncomputable section

namespace GlobalTheory.LiftCoker

theorem map_decomp_frob {O K : Type} [CommRing O] [NormedField K] [Algebra O K] (l : ℕ) [Fact l.Prime]
    {f : O⟦X⟧} {g : Fin l → O⟦X⟧}
    (h : f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j)) :
    PowerSeries.map (algebraMap O K) f =
      ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, map_X, map_expand]
  rfl

theorem colon_map_frob_le : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧),
    colon (O := O) (K := K) (G.map (frob K l)) ≤
      (colon (O := O) (K := K) G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G β hβ
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have decO : ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧,
      f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j) :=
    _root_.GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main l hl2 _ (fun f m => coeff_expand _ _ f)
  have uniqK : ∀ f : K⟦X⟧, ∃! g : Fin l → K⟦X⟧, f = ∑ j : Fin l, X ^ j.val * frob K l (g j) :=
    _root_.GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main l hl2 (frob K l) (fun f m => coeff_frob l f m)
  obtain ⟨b, hb, -⟩ := decO β
  have hbK := map_decomp_frob (K := K) l hb
  have key : ∀ j, b j ∈ colon (O := O) (K := K) G := by
    intro j w hw
    obtain ⟨M, hM, hMeq⟩ := hβ (frobV l w) (fun i => frob_mem_A l (hw i))
    have lift : ∀ k, ∃ μ : O⟦X⟧, PowerSeries.map (algebraMap O K) μ = M k := fun k => by
      obtain ⟨μ, hμ⟩ := (equivA O K).surjective ⟨M k, hM k⟩
      exact ⟨μ, by rw [← coe_equivA, hμ]⟩
    choose μ hμ using lift
    choose c hc using fun k => (decO (μ k)).exists
    have hMk : ∀ k, M k = ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (c k j)) :=
      fun k => by rw [← hμ k]; exact map_decomp_frob l (hc k)
    refine ⟨fun k => PowerSeries.map (algebraMap O K) (c k j), fun k => map_mem_A _, ?_⟩
    funext i
    have e1 := congrFun hMeq i
    simp only [Pi.smul_apply, smul_eq_mul, frobV_apply] at e1
    obtain ⟨g, -, hg⟩ := uniqK (PowerSeries.map (algebraMap O K) β * frob K l (w i))
    have E1 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (b j) * w i) := by
      rw [hbK, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_assoc]
    have E2 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val *
          frob K l ((G *ᵥ fun k => PowerSeries.map (algebraMap O K) (c k j)) i) := by
      rw [e1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hMk, Finset.mul_sum, map_sum, map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have h1 := hg _ E1
    have h2 := hg _ E2
    rw [Pi.smul_apply, smul_eq_mul]
    exact (congrFun h1 j).trans (congrFun h2 j).symm

  rw [hb]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (key j))

end GlobalTheory.LiftCoker
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientTorsionBounded
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

namespace GlobalTheory.LatticeQuotBound

theorem exists_pow_smul_mem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (T : Submodule O V) (hT : IsLatticeIn T)
    (ϖ : O) (hϖ : Irreducible ϖ) (v : V) : ∃ m : ℕ, ϖ ^ m • v ∈ T := by
  first
  | exact @_root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem
  | exact _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem ..)

theorem pow_smul_eq_zero_of_compact : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [TopologicalSpace V] [IsTopologicalAddGroup V] {X : Type} [TopologicalSpace X] [CompactSpace X] (T : Submodule O V), IsLatticeIn T → IsOpen (T : Set V) → ∀ ϖ : O, Irreducible ϖ → ∀ c : X → V ⧸ T, Continuous c → ∃ r : ℕ, ∀ x, ϖ ^ r • c x = 0 := by
  intro O _ _ _ V _ _ _ _ _ _ X _ _ T hT hTo ϖ hϖ c hc
  have hopen : ∀ m : ℕ, IsOpen {q : V ⧸ T | ϖ ^ m • q = 0} := by
    intro m
    have h : IsOpen ((Submodule.Quotient.mk : V → V ⧸ T) ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0}) := by
      rw [isOpen_iff_forall_mem_open]
      intro v hv
      refine ⟨(fun t => v + t) '' (T : Set V), ?_, isOpenMap_add_left v _ hTo,
        ⟨0, T.zero_mem, add_zero v⟩⟩
      rintro _ ⟨t, ht, rfl⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hv ⊢
      rw [Submodule.Quotient.mk_add, smul_add, hv, zero_add,
        (Submodule.Quotient.mk_eq_zero T).2 ht, smul_zero]
    exact isOpen_coinduced.mpr h
  have hcover : ∀ x, ∃ m : ℕ, x ∈ c ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0} := by
    intro x
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective T (c x)
    obtain ⟨m, hm⟩ := exists_pow_smul_mem T hT ϖ hϖ v
    refine ⟨m, ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hv, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero T).2 hm]
  have hmono : Monotone (fun m : ℕ => c ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0}) := by
    intro a b hab x hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    rw [← Nat.add_sub_cancel' hab, pow_add, mul_comm, mul_smul, hx, smul_zero]
  obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_cover _ (fun m => (hopen m).preimage hc)
    (fun x _ => Set.mem_iUnion.2 (hcover x)) hmono.directed_le
  exact ⟨m, fun x => hm (Set.mem_univ x)⟩

end GlobalTheory.LatticeQuotBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterCongrRootOfUnityPow
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

namespace GlobalTheory.LocDualInt

theorem exists_root_pow_cyclotomicCharacter_congr {p : ℕ} [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (g : Formalism.GaloisCohomology.GK p K) (k : ℕ) :
    ∃ ζ : PadicAlgCl p, ζ ^ (p ^ k) = 1 ∧ ∀ a : ℕ, g ζ = ζ ^ a → (a : ZMod (p ^ k)) =
      PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p
        (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) := by
  classical
  haveI : ∀ i : ℕ, HasEnoughRootsOfUnity (PadicAlgCl p) (p ^ i) := fun i => by
    haveI : NeZero ((p ^ i : ℕ) : PadicAlgCl p) :=
      ⟨by exact_mod_cast pow_ne_zero i (Fact.out : p.Prime).ne_zero⟩
    infer_instance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ k)
  refine ⟨ζ, hζ.pow_eq_one, fun a ha => ?_⟩
  set c : ZMod (p ^ k) := PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) with hc
  have hspec := cyclotomicCharacter.spec (L := PadicAlgCl p) p
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ hζ.pow_eq_one
  have hg : (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ = g ζ := rfl
  rw [hg, ha] at hspec
  have hpos : 0 < p ^ k := pow_pos (Fact.out : p.Prime).pos k
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ k, hpos, hζ.pow_eq_one⟩
  have hmod : a ≡ c.val [MOD orderOf ζ] := hfin.pow_eq_pow_iff_modEq.mp hspec
  rw [← hζ.eq_orderOf] at hmod
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod).trans (ZMod.natCast_zmod_val c)

end GlobalTheory.LocDualInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiagScaleApply
section
noncomputable section

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]


variable (K a ι) in
def diagScale (s : ZMod a → K) : Module.End K (Vec K a ι) where
  toFun v τ := s τ • v τ
  map_add' v w := by ext1 τ; simp [smul_add]
  map_smul' c v := by
    ext1 τ
    exact smul_comm (s τ) c (v τ)

@[simp] theorem diagScale_apply (s : ZMod a → K) (v : Vec K a ι) (τ : ZMod a) :
    diagScale K a ι s v τ = s τ • v τ := rfl

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

def isoProj {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e) : Module.End K (Vec K a ι) :=
  letI := Fintype.ofFinite (rootsOfUnity e K)
  (e : K)⁻¹ • ∑ ζ : rootsOfUnity e K,
    diagScale K a ι (fun τ => ((TameGal.inertia ζ : TameGal K l e a).root τ)⁻¹ ^ c.val) ∘ₗ
      Δ.act (TameGal.inertia ζ)

def Tsub {η H : ℕ} {D₁ : BKDat O K l e a ι η H} {D₂ : BKDat O K l e a κ η H} (F : BKHom D₁ D₂)
    (A' b : ℕ) : Submodule O (Vec K a κ) :=
  (F.imL.restrictScalars O).map ((mulV K a κ (((X : K⟦X⟧) ^ e) ^ A')).restrictScalars O) ⊔
    (D₂.L.restrictScalars O).map ((mulV K a κ ((l : K⟦X⟧) ^ b)).restrictScalars O) ⊔
    GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod

end GlobalTheory.CokerL

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

theorem act_vpow_smul {P : PhiMod O K l e a ι} (Δ : Descent P) (g : TameGal K l e a) (n : ℕ)
    (w : Vec K a ι) : Δ.act g (((X : K⟦X⟧) ^ e) ^ n • w) = ((X : K⟦X⟧) ^ e) ^ n • Δ.act g w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, ih, Δ.act_X_pow_smul, ← mul_smul, ← pow_succ]

theorem diagScale_smul (s : ZMod a → K) (f : K⟦X⟧) (w : Vec K a ι) :
    diagScale K a ι s (f • w) = f • diagScale K a ι s w := by
  ext1 τ
  exact smul_comm (s τ) f (w τ)

theorem isoProj_vpow {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e) (n : ℕ) (v : Vec K a ι) :
    isoProj Δ c (((X : K⟦X⟧) ^ e) ^ n • v) = ((X : K⟦X⟧) ^ e) ^ n • isoProj Δ c v := by
  letI := Fintype.ofFinite (rootsOfUnity e K)
  simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, act_vpow_smul, diagScale_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  exact smul_comm _ _ _

theorem app_isoProj {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P}
    {Δ₂ : Descent Q} (F : Descent.Hom Δ₁ Δ₂) (c : ZMod e) (v : Vec K a ι) :
    F.app (isoProj Δ₁ c v) = isoProj Δ₂ c (F.app v) := by
  letI := Fintype.ofFinite (rootsOfUnity e K)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.map_smul_of_tower, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [← F.app_act]
  ext1 τ
  simp only [diagScale_apply, BK.Hom.app_apply, Matrix.mulVec_smul]

end GlobalTheory.CokerL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowMulMemColonIdealFrobenius
section
noncomputable section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

namespace GlobalTheory.LiftCoker

theorem E_pow_mul_mem_colon_frob (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ)
    (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (τ : ZMod a) :
    ∀ α ∈ colon O K (F.mat τ),
      (X ^ e + (l : O⟦X⟧)) ^ (H + η) * α ∈ colon O K ((F.mat (τ - 1)).map (frob K l)) := by
  intro α hα w hw
  set x := D₂.mx τ *ᵥ w with hxdef
  have hx : x ∈ D₂.Lcomp τ := D₂.mem_extc.2 ⟨w, hw, rfl⟩
  have hxL : (Pi.single τ x : Vec K a κ) ∈ D₂.L := mem_tot.2 fun σ => by
    by_cases h : σ = τ
    · subst h
      simpa using hx
    · simp [h, zero_mem]
  have hup := mem_tot.1 (D₂.upper _ hxL) τ
  simp only [Pi.smul_apply, Pi.single_eq_same] at hup
  obtain ⟨m, hm, hαm⟩ := hα (E K l e ^ η • x) hup
  have hmM : (Pi.single τ m : Vec K a ι) ∈ D₁.M := mem_tot.2 fun σ => by
    by_cases h : σ = τ
    · subst h
      rw [Pi.single_eq_same]
      exact hm
    · simp [h, zero_mem]
  have hlow := mem_tot.1 (D₁.lower _ hmM) τ
  simp only [Pi.smul_apply, Pi.single_eq_same] at hlow
  obtain ⟨m', hm', hm'eq⟩ := D₁.mem_extc.1 hlow
  have hE : PowerSeries.map (algebraMap O K) ((X ^ e + (l : O⟦X⟧)) ^ (H + η) * α) =
      E K l e ^ (H + η) * PowerSeries.map (algebraMap O K) α := by
    simp [E, map_X, map_natCast]
  refine ⟨m', hm', ?_⟩
  · have key : D₂.mx τ *ᵥ (PowerSeries.map (algebraMap O K) ((X ^ e + (l : O⟦X⟧)) ^ (H + η) * α) • w) =
        D₂.mx τ *ᵥ ((F.mat (τ - 1)).map (frob K l) *ᵥ m') := by
      rw [Matrix.mulVec_smul, ← hxdef, hE, pow_add,
        show E K l e ^ H * E K l e ^ η * PowerSeries.map (algebraMap O K) α =
          E K l e ^ H * (PowerSeries.map (algebraMap O K) α * E K l e ^ η) by ring,
        mul_smul, mul_smul, hαm,
        ← Matrix.mulVec_smul, hm'eq, Matrix.mulVec_mulVec, F.comm, ← Matrix.mulVec_mulVec]
    have := congrArg (fun v => D₂.mxInv τ *ᵥ v) key
    rwa [Matrix.mulVec_mulVec (M := D₂.mxInv τ) (N := D₂.mx τ),
      Matrix.mulVec_mulVec (M := D₂.mxInv τ) (N := D₂.mx τ), PhiMod.mxInv_mul_mx,
      Matrix.one_mulVec, Matrix.one_mulVec] at this

end GlobalTheory.LiftCoker
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerEAddSmulMemEisensteinShiftGraded
section
noncomputable section

namespace GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ}


omit [CompleteSpace K] in
theorem conn_mem_ext_Rpi (D : BKDat O K l e a ι η H) {y : Vec K a ι}
    (hy : y ∈ D.ext (Rpi O K l e)) : D.conn y ∈ D.ext (Rpi O K l e) := by
  have hf : ∀ i τ, (Matrix.mulVec (D.mxInv τ) (y τ)) i ∈ Rpi O K l e := fun i τ =>
    D.mem_extc_iff.1 (mem_tot.1 hy τ) i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [D.eq_sum_phi_bas y, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hL : D.phi (bas i) ∈ D.L := D.phi_mem_L (D.bas_mem_M i)
  have hM : D.phi (bas i) ∈ D.MM := D.ext_mono (A_le_S l e) hL
  rw [PhiMod.conn_smul_tot]
  refine Submodule.add_mem _ ?_ ?_
  · exact D.smul_tot_mem_ext (fun τ => N_mem (derivative_mem_R l (hf i τ)))
      (D.ext_mono (S_le_R l e) hM)
  · exact D.smul_tot_mem_ext (hf i) (D.ext_mono (S_le_R l e) (D.conn_mem_MM hM))

omit [CompleteSpace K] in
theorem EN_add_smul_mem_shiftE' (D : BKDat O K l e a ι η H) (j : ℤ) (x : Vec K a ι)
    (hx : x ∈ shiftE l e j (D.ext (Rpi O K l e))) :
    D.EN x + ((j * e * l : ℤ) : K) • x ∈ shiftE l e (j + 1) (D.ext (Rpi O K l e)) := by
  rw [mem_shiftE] at hx ⊢
  set y := Ezpow K l e (-j) • x with hy
  have hxy : x = Ezpow K l e j • y := by
    rw [hy, smul_smul, mul_comm, Ezpow_neg_mul, one_smul]
  clear_value y
  clear hy
  have h1 : Ezpow K l e (j + 1) = Ezpow K l e j * E K l e := by
    rw [Ezpow_add, show Ezpow K l e 1 = E K l e from (Ezpow_natCast l e 1).trans (pow_one _)]
  have hc : ((j * e * l : ℤ) : K) • x = ((j * e * l : ℤ) : K⟦X⟧) • x := by
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hN : E K l e * N K (Ezpow K l e j) + ((j * e * l : ℤ) : K⟦X⟧) * Ezpow K l e j =
      Ezpow K l e (j + 1) * ((j * e : ℤ) : K⟦X⟧) := by
    rw [E_mul_N_Ezpow, N_E, h1, E]
    push_cast
    ring
  have key : D.EN x + ((j * e * l : ℤ) : K) • x =
      Ezpow K l e (j + 1) • ((j * e : ℤ) • y + D.conn y) := by
    rw [hc, PhiMod.EN_apply, hxy, PhiMod.conn_smul, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
      ← Int.cast_smul_eq_zsmul K⟦X⟧ (j * e : ℤ), smul_smul, ← hN, add_smul, h1, mul_comm (E K l e) (Ezpow K l e j)]
    abel
  rw [key, smul_smul, Ezpow_neg_mul, one_smul]
  exact Submodule.add_mem _ (zsmul_mem hx _) (conn_mem_ext_Rpi D hx)

theorem EN_add_smul_mem_shiftE :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℤ) (x : Vec K a ι), x ∈ shiftE l e j (D.ext (Rpi O K l e)) → D.EN x + ((j * e * l : ℤ) : K) • x ∈ shiftE l e (j + 1) (D.ext (Rpi O K l e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D j x hx
  exact EN_add_smul_mem_shiftE' D j x hx

end GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsXPowSmulEqPrimePowSmulPhiModuleStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_X_pow_smul_eq_prime_pow_smul_phiModule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (n : ℕ), ∀ w ∈ P.MM, ∃ w' ∈ P.MM, (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w = (l : K) ^ (l ^ n) • w' := by
  first | exact @GlobalTheory.BK.PhiMod.exists_X_pow_smul_eq_l_pow_smul | exact GlobalTheory.BK.PhiMod.exists_X_pow_smul_eq_l_pow_smul | (intros; apply GlobalTheory.BK.PhiMod.exists_X_pow_smul_eq_l_pow_smul <;> assumption)
end

