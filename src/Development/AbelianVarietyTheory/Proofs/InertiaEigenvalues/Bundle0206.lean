module

public import Mathlib
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0202
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LevelRepFormula
section
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg.SeqCount

open Formalism.NG ReciprocityTheory.ChartRestriction.T2

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module O M]

theorem exists_pow_smul_eq {ϖ : O} (hdiv : ∀ m : M, ∃ m' : M, ϖ • m' = m) (n : ℕ) (m : M) :
    ∃ m' : M, ϖ ^ n • m' = m := by
  induction n generalizing m with
  | zero => exact ⟨m, by rw [pow_zero, one_smul]⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih m
    obtain ⟨b, hb⟩ := hdiv a
    exact ⟨b, by rw [pow_succ, mul_smul, hb, ha]⟩

theorem lev_val_injective {c : O} : Function.Injective (Lev.val : Lev M c → M) :=
  fun _ _ h => Lev.ext h

def levelCocycleToModuleCocycle (ρ : Representation O G M) (c : O) : Z1 (levRep ρ c) →ₗ[O] coZ1s ρ where
  toFun f := ⟨fun g => (f.1 g).val, fun g h => by
    have := ((mem_Z1_iff_cocycle _ _).1 f.2).2 g h
    show (f.1 (g * h)).val = (f.1 g).val + ρ g (f.1 h).val
    rw [this, Lev.val_add, levRep_val]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def levelH1ToModuleH1 (ρ : Representation O G M) (c : O) : H1 (levRep ρ c) →ₗ[O] H1z ρ :=
  Submodule.mapQ _ _ (levelCocycleToModuleCocycle ρ c) (by
    intro f hf
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hf
    exact ⟨m.val, funext fun g => by
      have h2 : f.1 g = levRep ρ c g m - m := hm g
      show ρ g m.val - m.val = (f.1 g).val
      rw [h2]; rfl⟩)

theorem valuation_H1_mk (ρ : Representation O G M) (c : O) (f : Z1 (levRep ρ c)) :
    levelH1ToModuleH1 ρ c (Submodule.Quotient.mk f) = Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c f) := rfl

theorem valuation_H1_mem (ρ : Representation O G M) (c : O) (x : H1 (levRep ρ c)) : levelH1ToModuleH1 ρ c x ∈ HcLC ρ := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨levelCocycleToModuleCocycle ρ c f, ?_, rfl⟩
  show IsLocallyConstant (fun g => (f.1 g).val)
  have h1 : IsLocallyConstant f.1 := (IsLocallyConstant.iff_continuous f.1).2 ((mem_Z1_iff_cocycle _ _).1 f.2).1
  exact h1.comp _

theorem smul_valuation_H1 (ρ : Representation O G M) (c : O) (x : H1 (levRep ρ c)) : c • levelH1ToModuleH1 ρ c x = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [valuation_H1_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨0, funext fun g => ?_⟩
  show ρ g 0 - 0 = c • (f.1 g).val
  rw [Lev.smul_val, map_zero, sub_zero]

def phi (ρ : Representation O G M) (c : O) :
    H1 (levRep ρ c) →ₗ[O] LinearMap.ker (c • LinearMap.id : HcLC ρ →ₗ[O] HcLC ρ) :=
  LinearMap.codRestrict _ (LinearMap.codRestrict (HcLC ρ) (levelH1ToModuleH1 ρ c) (valuation_H1_mem ρ c)) (fun x => by
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    exact Subtype.ext (smul_valuation_H1 ρ c x))

theorem phi_surjective (ρ : Representation O G M) (c : O) (hdiv : ∀ m : M, ∃ m' : M, c • m' = m)
    (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) : Function.Surjective (phi ρ c) := by
  rintro ⟨⟨y, hy⟩, hk⟩
  obtain ⟨z, hz, rfl⟩ := hy
  have hk' : c • (Submodule.mkQ _ z : H1z ρ) = 0 := by
    have := congrArg Subtype.val (LinearMap.mem_ker.1 hk)
    simpa using this
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hk'
  obtain ⟨m, hm⟩ := hk'
  obtain ⟨m', hm'⟩ := hdiv m
  have hz2 : ∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h) := z.2
  have hzlc : IsLocallyConstant (z.1 : G → M) := hz
  let w : G → M := fun g => z.1 g - (ρ g m' - m')
  have hw : ∀ g, c • w g = 0 := fun g => by
    have h1 : ρ g m - m = c • z.1 g := congrFun hm g
    show c • (z.1 g - (ρ g m' - m')) = 0
    rw [smul_sub, smul_sub, ← map_smul (ρ g) c m', hm', h1, sub_self]
  have hwlc : IsLocallyConstant w := hzlc.sub ((hlc m').sub (IsLocallyConstant.const m'))
  have hwc : ∀ g h, w (g * h) = w g + ρ g (w h) := fun g h => by
    show z.1 (g * h) - (ρ (g * h) m' - m') = (z.1 g - (ρ g m' - m')) + ρ g (z.1 h - (ρ h m' - m'))
    rw [hz2, map_mul, Module.End.mul_apply, map_sub, map_sub]
    abel
  have hf : (fun g => Lev.mk (w g) (hw g) : G → Lev M c) ∈ Z1 (levRep ρ c) := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨?_, fun g h => Lev.ext ?_⟩
    · exact (IsLocallyConstant.desc _ Lev.val hwlc lev_val_injective).continuous
    · show w (g * h) = w g + ρ g (w h)
      exact hwc g h
  refine ⟨Submodule.Quotient.mk ⟨_, hf⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  show levelH1ToModuleH1 ρ c (Submodule.Quotient.mk ⟨_, hf⟩) = Submodule.mkQ _ z
  rw [valuation_H1_mk, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine ⟨-m', funext fun g => ?_⟩
  show ρ g (-m') - -m' = (z.1 g - (ρ g m' - m')) - z.1 g
  rw [map_neg]
  abel

def preInv (ρ : Representation O G M) (c : O) : Submodule O M :=
  ρ.invariants.comap (c • LinearMap.id : M →ₗ[O] M)

theorem mem_preInv {ρ : Representation O G M} {c : O} (m : M) :
    m ∈ preInv ρ c ↔ ∀ g, ρ g (c • m) = c • m := Iff.rfl

theorem smul_cob_eq_zero {ρ : Representation O G M} {c : O} (m : preInv ρ c) (g : G) :
    c • (ρ g m.1 - m.1) = 0 := by
  rw [smul_sub, ← map_smul (ρ g) c, (mem_preInv _).1 m.2 g, sub_self]

def cobLev (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    preInv ρ c →ₗ[O] Z1 (levRep ρ c) where
  toFun m := ⟨fun g => Lev.mk (ρ g m.1 - m.1) (smul_cob_eq_zero m g), by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨?_, fun g h => Lev.ext ?_⟩
    · exact (IsLocallyConstant.desc _ Lev.val ((hlc m.1).sub (IsLocallyConstant.const m.1))
        lev_val_injective).continuous
    · show ρ (g * h) m.1 - m.1 = (ρ g m.1 - m.1) + ρ g (ρ h m.1 - m.1)
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel⟩
  map_add' a b := Subtype.ext (funext fun g => Lev.ext (by
    show ρ g (a.1 + b.1) - (a.1 + b.1) = (ρ g a.1 - a.1) + (ρ g b.1 - b.1)
    rw [map_add (f := _)]; abel))
  map_smul' r a := Subtype.ext (funext fun g => Lev.ext (by
    show ρ g (r • a.1) - r • a.1 = r • (ρ g a.1 - a.1)
    rw [map_smul, smul_sub]))

def kappa (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    preInv ρ c →ₗ[O] H1 (levRep ρ c) :=
  (Submodule.mkQ _) ∘ₗ cobLev ρ c hlc

theorem ker_valuation_H1 (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    LinearMap.ker (levelH1ToModuleH1 ρ c) = LinearMap.range (kappa ρ c hlc) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : (Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c f) : H1z ρ) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨m, hm⟩ := h1
    have hm' : ∀ g, ρ g m - m = (f.1 g).val := fun g => congrFun hm g
    have hP : m ∈ preInv ρ c := (mem_preInv m).2 fun g => by
      have := congrArg (c • ·) (hm' g)
      simp only [Lev.smul_val, smul_sub] at this
      rw [map_smul, ← sub_eq_zero, ← this]
    refine ⟨⟨m, hP⟩, ?_⟩
    show Submodule.Quotient.mk (cobLev ρ c hlc ⟨m, hP⟩) = Submodule.Quotient.mk f
    congr 1
    exact Subtype.ext (funext fun g => Lev.ext (hm' g))
  · rintro x ⟨m, rfl⟩
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c (cobLev ρ c hlc m)) : H1z ρ) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨m.1, rfl⟩

def toQ (ρ : Representation O G M) (c : O) :
    preInv ρ c →ₗ[O] (ρ.invariants ⧸ LinearMap.range (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) :=
  (Submodule.mkQ _) ∘ₗ (LinearMap.codRestrict ρ.invariants
    ((c • LinearMap.id : M →ₗ[O] M) ∘ₗ (preInv ρ c).subtype) (fun m =>
      (Representation.mem_invariants _ _).2 ((mem_preInv _).1 m.2)))

theorem toQ_surjective (ρ : Representation O G M) (c : O) (hdiv : ∀ m : M, ∃ m' : M, c • m' = m) :
    Function.Surjective (toQ ρ c) := by
  intro y
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨m, hm⟩ := hdiv t.1
  have hP : m ∈ preInv ρ c := (mem_preInv m).2 fun g => by
    rw [hm]; exact (Representation.mem_invariants _ _).1 t.2 g
  refine ⟨⟨m, hP⟩, ?_⟩
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext hm

theorem ker_kappa (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    LinearMap.ker (kappa ρ c hlc) = LinearMap.ker (toQ ρ c) := by
  ext m
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h
    have h1 : (Submodule.Quotient.mk (cobLev ρ c hlc m) : H1 (levRep ρ c)) = 0 := h
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨ℓ, hℓ⟩ := (mem_coboundaries1 _ _).1 h1
    have hℓ' : ∀ g, ρ g m.1 - m.1 = ρ g ℓ.val - ℓ.val := fun g => congrArg Lev.val (hℓ g)
    have hinv : m.1 - ℓ.val ∈ ρ.invariants := (Representation.mem_invariants _ _).2 fun g => by
      rw [map_sub]; exact sub_eq_sub_iff_sub_eq_sub.mp (hℓ' g)
    show Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨m.1 - ℓ.val, hinv⟩, Subtype.ext ?_⟩
    show c • (m.1 - ℓ.val) = c • m.1
    rw [smul_sub, Lev.smul_val, sub_zero]
  · intro h
    have h1 : (Submodule.Quotient.mk _ : ρ.invariants ⧸ LinearMap.range
        (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) = 0 := h
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨t, ht⟩ := h1
    have ht' : c • t.1 = c • m.1 := congrArg Subtype.val ht
    have hl : c • (m.1 - t.1) = 0 := by rw [smul_sub, ht', sub_self]
    show (Submodule.Quotient.mk (cobLev ρ c hlc m) : H1 (levRep ρ c)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine (mem_coboundaries1 _ _).2 ⟨Lev.mk (m.1 - t.1) hl, fun g => Lev.ext ?_⟩
    show ρ g m.1 - m.1 = ρ g (m.1 - t.1) - (m.1 - t.1)
    rw [map_sub, (Representation.mem_invariants _ _).1 t.2 g]
    abel

theorem card_H1_level_rep_eq : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O) (n : ℕ),
    (∀ m : M, ∃ m' : M, ϖ • m' = m) → (∀ m : M, IsLocallyConstant (fun g => ρ g m)) →
    Finite (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) →
    Finite (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) ∧
    Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) =
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) *
      Nat.card (ρ.invariants ⧸ LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := by
  intro O _ G _ _ M _ _ ρ ϖ n hdiv hlc hfin
  have hdivc := exists_pow_smul_eq hdiv n
  have hs := phi_surjective ρ (ϖ ^ n) hdivc hlc
  refine ⟨Finite.of_surjective _ hs, ?_⟩
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (phi ρ (ϖ ^ n))),
    Nat.card_congr ((phi ρ (ϖ ^ n)).quotKerEquivOfSurjective hs).toEquiv, mul_comm]
  congr 1
  have hker : LinearMap.ker (phi ρ (ϖ ^ n)) = LinearMap.range (kappa ρ (ϖ ^ n) hlc) := by
    rw [phi, LinearMap.ker_codRestrict, LinearMap.ker_codRestrict, ker_valuation_H1]
  rw [hker]
  exact Nat.card_congr (((kappa ρ (ϖ ^ n) hlc).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_kappa ρ (ϖ ^ n) hlc)).trans
      ((toQ ρ (ϖ ^ n)).quotKerEquivOfSurjective (toQ_surjective ρ (ϖ ^ n) hdivc)))).toEquiv)

end GlobalTheory.ShapeNeg.SeqCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2EqSameAction
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.H2CardScalars

theorem card_H2_eq_of_same_action {R S : Type} [CommRing R] [CommRing S] {G : Type} [Group G]
    [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module R M] [Module S M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [ContinuousConstSMul S M]
    (rho : Representation R G M) (rho' : Representation S G M)
    (h : ∀ g m, rho g m = rho' g m) : Nat.card (H2 rho) = Nat.card (H2 rho') := by
  have hZ : ∀ f : G × G → M, f ∈ Z2 rho ↔ f ∈ Z2 rho' := by
    intro f; rw [mem_cocycles2, mem_cocycles2]; simp only [h]
  have hd : ∀ c : G → M, d1 rho c = d1 rho' c := fun c => funext fun p => by
    simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, h]
  have hB : ∀ f : G × G → M, f ∈ B2 rho ↔ f ∈ B2 rho' := by
    intro f; rw [separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]; simp only [hd]
  let e : Z2 rho ≃ Z2 rho' := Equiv.subtypeEquiv (Equiv.refl _) hZ
  apply Nat.card_congr
  refine Quotient.congr e ?_
  intro a b
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
  simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub]
  exact hB _

end GlobalTheory.H2CardScalars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixTopnilStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_integral_matrix_topnil : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → ∀ w : Matrix (Fin n) (Fin n) E, w * N = N * w → (∀ i j, ‖w i j‖ ≤ 1) → ∀ M : ℕ, (∀ i j, ‖(w ^ M) i j‖ < 1) → ∀ i j, ‖w i j‖ < 1 := by
  first | exact @GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute | exact GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute | (intros; apply GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCyclotomicCharacterLocalGalois
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.FunctorialityH2

theorem cyc_char_continuous {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    {G : Type} [Group G] [TopologicalSpace G] (hO : PadicCoeff p O) (i : G ≃ₜ* GK p K)
    {ε : G →* Oˣ} (hc : IsCyc p K (carry i ε)) :
    Continuous (fun g : G => ((ε g : Oˣ) : O)) := by
  have := hO.ring
  set ε' : GK p K →* Oˣ := carry i ε with hε'
  have key : ∀ k : ℕ, ∃ H : Subgroup (GK p K), IsOpen (H : Set (GK p K)) ∧
      ∀ h ∈ H, ((ε' h : Oˣ) : O) - 1 ∈ Ideal.span {(p : O) ^ k} := by
    intro k
    have hN : 0 < p ^ k := pow_pos hp.out.pos k
    haveI : NeZero ((p ^ k : ℕ) : PadicAlgCl p) := ⟨by exact_mod_cast hN.ne'⟩
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (p ^ k) (PadicAlgCl p))
      (Polynomial.degree_cyclotomic_pos (p ^ k) (PadicAlgCl p) hN).ne'
    have hpr : IsPrimitiveRoot ζ (p ^ k) := Polynomial.isRoot_cyclotomic_iff.1 hζ
    have hint : IsIntegral K ζ :=
      IsIntegral.of_pow hN (by rw [hpr.pow_eq_one]; exact isIntegral_one)
    haveI := IntermediateField.adjoin.finiteDimensional hint
    refine ⟨(IntermediateField.adjoin K {ζ}).fixingSubgroup,
      IntermediateField.fixingSubgroup_isOpen _, fun h hh => ?_⟩
    have hfix : h ζ = ζ := hh ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩
    obtain ⟨a, ha, hmem⟩ := hc h k ζ hpr.pow_eq_one
    have hz : ζ ≠ 0 := hpr.ne_zero hN.ne'
    have h1 : ζ ^ ((a : ℤ) - 1) = 1 := by
      rw [zpow_sub₀ hz, zpow_natCast, zpow_one, ← ha, hfix, div_self hz]
    obtain ⟨c, hcdef⟩ := (hpr.zpow_eq_one_iff_dvd _).1 h1
    have h2 : ((a : O) - 1) = ((p : O) ^ k) * (c : O) := by
      have := congrArg (fun z : ℤ => (z : O)) hcdef
      push_cast at this
      exact this
    have h3 : ((ε' h : Oˣ) : O) - 1 = (((ε' h : Oˣ) : O) - a) + ((a : O) - 1) := by ring
    rw [h3, h2]
    exact Ideal.add_mem _ hmem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hcont' : Continuous (fun g : GK p K => ((ε' g : Oˣ) : O)) := by
    rw [continuous_iff_continuousAt]
    intro g0
    rw [ContinuousAt, Filter.tendsto_def]
    intro U hU
    have hV : (fun o : O => ((ε' g0 : Oˣ) : O) + o) ⁻¹' U ∈ nhds (0 : O) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨m, hm⟩ := (isAdic_iff.1 hO.adic).2 _ hV
    obtain ⟨H, hHo, hH⟩ := key m
    have hle : Ideal.span {(p : O) ^ m} ≤ IsLocalRing.maximalIdeal O ^ m :=
      (Ideal.span_singleton_le_iff_mem _).2 (Ideal.pow_mem_pow hO.p_mem m)
    refine Filter.mem_of_superset
      ((hHo.preimage (continuous_const_mul g0⁻¹)).mem_nhds (by simpa using H.one_mem)) ?_
    intro g hg
    have h1 := hH _ hg
    have h2 : ((ε' g : Oˣ) : O) - (ε' g0 : O) ∈ Ideal.span {(p : O) ^ m} := by
      have e : ((ε' g : Oˣ) : O) - (ε' g0 : O) =
          (ε' g0 : O) * (((ε' (g0⁻¹ * g) : Oˣ) : O) - 1) := by
        rw [map_mul, Units.val_mul, mul_sub, ← mul_assoc, ← Units.val_mul, ← map_mul,
          mul_inv_cancel, map_one, Units.val_one, one_mul, mul_one]
      rw [e]
      exact Ideal.mul_mem_left _ _ h1
    have h3 := hm (hle h2)
    simpa using h3
  have e : (fun g : G => ((ε g : Oˣ) : O)) = (fun g : GK p K => ((ε' g : Oˣ) : O)) ∘ i := by
    funext g
    simp only [Function.comp_apply, hε', carry, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    first
    | rw [ContinuousMulEquiv.symm_apply_apply]
    | exact congrArg (fun x => ((ε x : Oˣ) : O)) (i.toMulEquiv.symm_apply_apply g).symm
  rw [e]
  exact hcont'.comp i.continuous

end GlobalTheory.FunctorialityH2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerTraceAlmostSurjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicTower_trace_almost_surjective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)), Kinf K ≤ L → (∀ h ∈ Hinf K, ∀ x ∈ L, h x ∈ L) → (∀ s ∈ S, s ∈ Hinf K) → (∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) → ∀ a : Om l, a ∈ Kinf K → ‖a‖ < 1 → ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a := by
  first | exact @GlobalTheory.Cyc.trace_almost_onto | exact GlobalTheory.Cyc.trace_almost_onto | (intros; apply GlobalTheory.Cyc.trace_almost_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DedekindZetaEulerProductMulSubOneEntireNeZero
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
private lemma dedekindZeta_eq_exp_tsum_neg_log (K : Type) [Field K] [NumberField K] (s : ℂ)
    (hs : 1 < s.re) :
    dedekindZeta K s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  have hs0 : -s ≠ 0 := by
    intro h
    rw [neg_eq_zero.mp h] at hs
    norm_num at hs
  have key := _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K (fun I => if I = ⊥ then 0 else 1)
    (by simp) (by simp) (fun I J => by
      by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;> simp [hI, hJ, Ideal.mul_eq_bot])
    (fun I => by split_ifs <;> simp) s hs
  rw [_root_.GlobalTheory.Mem.ZetaPole.dedekindZeta_eq_tsum_ideal K hs]
  convert key using 1
  · refine tsum_congr fun I => ?_
    by_cases hI : I = ⊥
    · simp [hI, Complex.zero_cpow hs0]
    · simp [hI]
  · congr 1
    refine tsum_congr fun P => ?_
    simp [P.ne_bot]


open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
theorem _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero :
    ∀ (K : Type) [Field K] [NumberField K], ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  intro K _ _
  obtain ⟨Z, hZd, hZ⟩ := _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K
  refine ⟨Z, hZd, ?_, hZ⟩
  have h1 : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (Z 1)) := by
    have : Continuous fun s : ℝ => Z s := hZd.continuous.comp Complex.continuous_ofReal
    simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (dedekindZeta_residue K : ℂ)) := by
    refine (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1 < (s : ℂ).re := by simpa using hs
    rw [hZ s hs', dedekindZeta_eq_exp_tsum_neg_log K s hs']
  rw [tendsto_nhds_unique h1 h2]
  exact_mod_cast dedekindZeta_residue_ne_zero K

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobAtPlaceOverPrime
section
open ReciprocityTheory.Gal Pointwise NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_frob_at_place_over_prime : ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω),
    A.valuation (p : Ω) < 1 → ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∃ q : ℕ, q ≠ 1 ∧
      ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1 := by
  intro F Ω _ _ _ _ _ p hp A hpA
  set f : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F) with hf
  have fA : ∀ r : 𝓞 F, f r ∈ A := fun r =>
    mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe r).map (algebraMap F Ω).toIntAlgHom)
  let I : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal A).comap (f.codRestrict A fA)
  have memI : ∀ r, r ∈ I ↔ A.valuation (algebraMap F Ω (r : F)) < 1 := fun r => by
    simp only [I, Ideal.mem_comap]; exact A.valuation_lt_one_iff _
  have hIp : I.IsPrime := Ideal.comap_isPrime _ _
  have hpI : (p : 𝓞 F) ∈ I := by
    rw [memI]; simpa using hpA
  have hIne : I ≠ ⊥ := fun h => by
    have h' := hpI
    rw [h, Ideal.mem_bot] at h'
    exact hp.out.ne_zero (by exact_mod_cast h')
  let v : HeightOneSpectrum (𝓞 F) := ⟨I, hIp, hIne⟩
  obtain ⟨σ, hσA, hσ⟩ := exists_frob_over (F := F) (A := A) (v := v) (fun x => (memI x).symm)
  refine ⟨σ, hσA, Nat.card (𝓞 F ⧸ v.asIdeal), fun h1 => ?_, hσ⟩
  have hss : Subsingleton (𝓞 F ⧸ v.asIdeal) := by
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [h1]; exact one_ne_zero)
    exact Finite.card_le_one_iff_subsingleton.mp h1.le
  have : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]; exact Subsingleton.elim _ _
  exact hIp.ne_top ((Ideal.eq_top_iff_one _).2 this)

end GlobalTheory
end

