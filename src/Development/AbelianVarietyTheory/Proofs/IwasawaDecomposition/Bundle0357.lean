module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
public import Formalism.LocalToGlobal.Columns.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Formalism.LocalToGlobal.Columns.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

section Cut

variable {G Γ : Type} [Group G] [Group Γ] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def cutSp (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (Q : Subgroup G) (ch : Q →* ℂˣ)
    {G₀ : Type} [Group G₀] (red : Q →* G₀) (P : Subgroup G₀) (ψ : P →* ℂˣ) : Submodule ℂ (G → W) :=
  Bridge.AdForms ι ρ J χ ⊓
    { carrier := {F | ∀ (κ : Q) (hκ : red κ ∈ P) (h : G), F (h * κ) = ((ch κ * ψ ⟨red κ, hκ⟩ : ℂˣ) : ℂ) • F h}
      add_mem' := fun {F F'} hF hF' κ hκ h => by simp only [Pi.add_apply, hF κ hκ h, hF' κ hκ h, smul_add]
      zero_mem' := fun κ hκ h => by simp
      smul_mem' := fun c F hF κ hκ h => by simp only [Pi.smul_apply, hF κ hκ h]; rw [smul_comm] }

def lvlForm {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G₀ : Type} [Group G₀] [Fintype G₀]
    (r : Representation K G₀ S.Forms) (P : Subgroup G₀) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) : S.Forms :=
  S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x)

end Cut

variable {D : D7}


variable (D) in
def km (n : ℕ) : Formalism.AUTREP.GAf D.host.E n →* GL (Fin n) (EAf D) := (ReciprocityTheory.Aut.GA D.host.E n).subtype

def stdJ {n : ℕ} (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n) : Subgroup (Formalism.AUTREP.GAf D.host.E n) :=
  (Formalism.L2.DIV.lev D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld).comap (km D n)

def stdX {n : ℕ} (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n) : stdJ Ld →* ℂˣ :=
  (Formalism.L2.DIV.levChar D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld).comp ((km D n).subgroupComap _)


variable (D) in
def datV (n : ℕ) (hr : D.R.r ≤ n) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ)
    (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Formalism.L2.DIV.LevDat D.host.E ℂ n :=
  datY n D.R.r D.R.t 1 hr Pg Q P (fun _ => chi) xi Frm.A

def UnitFr {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) : Prop := ∀ κ, finE V (P.ψ κ) = km D V.rank κ

def toGf {V : HSp D} {n : ℕ} (P : principalLevelFrame.RowPsi V n) : Formalism.AUTREP.GAf D.host.E n →* Bridge.Gf V :=
  (finHom V).rangeRestrict.comp P.ψ

def RatIso {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V) : Prop :=
  ∀ γ : ReciprocityTheory.Aut.GQ D.host.E V.rank, Bridge.ratF V (e γ) = toGf P γ.1 ∧
    ∀ γ₀ : GL (Fin V.rank) D.host.E,
      (γ.1.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) =
        (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom →
      Bridge.IsRatMat V (e γ) γ₀

def wtRep {V : HSp D} {n : ℕ} (c : CoefA V) (e : ReciprocityTheory.Aut.GQ D.host.E n ≃* Formalism.L2.Theta.GQ V) :
    Representation ℂ (ReciprocityTheory.Aut.GQ D.host.E n) c.W :=
  c.coef.ρ.comp e.toMonoidHom

end GlobalTheory.MtIn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgebraicRootsCoeffFieldContainsTwistValue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.RootsIn

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.Mem.Col2
open ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

def finOr {α : Type} (s : Set α) : Finset α := by
  classical
  exact if h : s.Finite then h.toFinset else ∅

theorem mem_finOr {α : Type} {s : Set α} (h : s.Finite) {x : α} : x ∈ finOr s ↔ x ∈ s := by
  unfold finOr
  rw [dite_eq_left h, Set.Finite.mem_toFinset]

def rootN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

theorem rootN_isAlgebraic (N : ℕ) : IsAlgebraic ℚ (rootN N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [rootN, Nat.cast_zero, div_zero, Complex.exp_zero]
    exact isAlgebraic_one
  · have h : rootN N ^ N = 1 := (Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one
    exact (IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)).isAlgebraic

def ramSet {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) : Set (HeightOneSpectrum (𝓞 E)) :=
  {Q | ¬ χ.UnrAt Q}

def overN {E : Type} [Field E] [NumberField E] (n : ℕ) : Set (HeightOneSpectrum (𝓞 E)) :=
  {Q' | ((n : ℕ) : 𝓞 E) ∈ Q'.asIdeal}

def rootsOf {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) : Finset ℂ := by
  classical
  exact (finOr (ramSet χ)).biUnion fun Q =>
    (finOr (overN (E := E) (Ideal.absNorm Q.asIdeal))).image fun Q' => rootN (Nat.card (kP Q'))

def Sv (P : Pre) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : Finset ℂ := by
  classical
  exact (finOr Ξ).biUnion rootsOf

theorem isAlgebraic_of_mem_Sv (P : Pre) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) (z : ℂ) (hz : z ∈ Sv P Ξ) : IsAlgebraic ℚ z := by
  unfold Sv at hz
  obtain ⟨χ, -, hχ⟩ := Finset.mem_biUnion.1 hz
  unfold rootsOf at hχ
  obtain ⟨Q, -, hQ⟩ := Finset.mem_biUnion.1 hχ
  obtain ⟨Q', -, rfl⟩ := Finset.mem_image.1 hQ
  exact rootN_isAlgebraic _

theorem ramSet_finite {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) : (ramSet χ).Finite := by
  have h := GlobalTheory.HeckeSplit.eventually_unrAt χ.1 χ.2.1
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun Q hQ => ?_
  simp only [ramSet, Set.mem_setOf_eq] at hQ ⊢
  rwa [GlobalTheory.HeckeSplit.unrAt_iff]

theorem overN_finite {E : Type} [Field E] [NumberField E] {n : ℕ} (hn : n ≠ 0) : (overN (E := E) n).Finite := by
  have hne : (Ideal.span {((n : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors hne).subset fun Q hQ => ?_
  simp only [overN, Set.mem_setOf_eq] at hQ ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hQ

theorem exists_ram {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K] {σ : K →+* ℂ}
    {μ : Chr F E K} {ξ : Formalism.L2.Host.HChar E} (h : Reads σ μ ξ) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ Qprime μ) :
    ∃ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v ∧ ¬ ξ.UnrAt Q := by
  by_contra hne
  push_neg at hne
  simp only [Qprime, Set.mem_setOf_eq] at hv
  apply hv
  intro x hx
  rw [MonoidHom.mem_ker]
  obtain ⟨a, rfl⟩ := finAf_surjective F E x
  simp only [inertAt, Subgroup.mem_inf] at hx
  obtain ⟨hx1, hx2⟩ := hx

  have hcomp : ∀ P : HeightOneSpectrum (𝓞 E),
      ((GlobalTheory.HeckeSplit.finPart E P a : (P.adicCompletion E)ˣ) : P.adicCompletion E) =
        afIso F E (finAf F E a : AfE F E) P := by
    intro P
    rw [afIso_finAf]
    rfl

  have key : ξ.1 a = ξ.1 (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E a)) := by
    rw [GlobalTheory.HeckeSplit.char_eq_prod_local ξ.1 ξ.2.1 a ∅ ?_, Finset.prod_empty, mul_one]
    intro P _
    by_cases hPv : P.under (𝓞 F) = v
    · apply (GlobalTheory.HeckeSplit.unrAt_iff E ξ P).2 (hne P hPv)
      rw [hcomp]
      simp only [intU, Submonoid.mem_units_iff] at hx1
      have h1 := (mem_rInt_iff F E _).1 hx1.1 P
      have h2 := (mem_rInt_iff F E _).1 hx1.2 P
      have hprod : afIso F E (finAf F E a : AfE F E) P *
          afIso F E (((finAf F E a)⁻¹ : (AfE F E)ˣ) : AfE F E) P = 1 := by
        have h : afIso F E ((finAf F E a : AfE F E) * (((finAf F E a)⁻¹ : (AfE F E)ˣ) : AfE F E)) P = 1 := by
          rw [Units.mul_inv, map_one]
          rfl
        rw [map_mul] at h
        exact h
      have hv' : Valued.v (afIso F E (finAf F E a : AfE F E) P) *
          Valued.v (afIso F E (((finAf F E a)⁻¹ : (AfE F E)ˣ) : AfE F E) P) = 1 := by
        rw [← map_mul, hprod, map_one]
      refine le_antisymm h1 ?_
      calc (1 : _) = _ := hv'.symm
        _ ≤ Valued.v (afIso F E (finAf F E a : AfE F E) P) * 1 := by gcongr
        _ = _ := mul_one _
    · have h1 : GlobalTheory.HeckeSplit.finPart E P a = 1 := by
        apply Units.ext
        rw [hcomp, Units.val_one]
        exact (mem_suppAt_iff F E v _).1 hx2 P hPv
      rw [h1, map_one, map_one]
  have hb : finAf F E (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E a)) = 1 := by
    apply Units.ext
    apply (afIso F E).injective
    rw [afIso_finAf, Units.val_one, map_one]
    rfl
  have e1 := h a
  have e2 := h (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E a))
  rw [hb, map_one, Units.val_one, map_one] at e2
  rw [key, e2] at e1
  apply Units.ext
  rw [Units.val_one]
  apply σ.injective
  rw [map_one]
  exact e1.symm

end GlobalTheory.Mem.Col2.RootsIn


open GlobalTheory.Mem.Col2.RootsIn in
theorem GlobalTheory.Mem.Col2.exists_roots_valsIn : ∃ Sv : ∀ P : Pre, Set (Formalism.L2.Host.HChar P.host.E) → Finset ℂ, (∀ P Ξ, ∀ z ∈ Sv P Ξ, IsAlgebraic ℚ z) ∧
  ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), I.Ok → (∀ z ∈ Sv B.toPre (Set.range I.xi), z ∈ B.LLC) → ValsIn I := by
  refine ⟨GlobalTheory.Mem.Col2.RootsIn.Sv, fun P Ξ z hz => isAlgebraic_of_mem_Sv P Ξ z hz, ?_⟩
  intro B px I hI hS
  refine ⟨?_, ?_⟩
  ·
    intro a P _
    exact ⟨_, (hI.xi_reads a _).symm⟩
  · intro a P hP
    obtain ⟨v, hv, hsel, -⟩ := I.exists_of_mem_Q hP
    obtain ⟨Q, hQv, hQ⟩ := exists_ram (hI.xi_reads a) hv
    have hPv : P.asIdeal.under (𝓞 B.fields.F) = v.asIdeal := hsel ▸ hI.sel_ok v

    have hQP : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
      have h2 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 B.fields.F) ∈ P.asIdeal.under (𝓞 B.fields.F) := by
        rw [hPv, ← hQv]
        show _ ∈ Ideal.comap (algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E)) Q.asIdeal
        rw [Ideal.mem_comap, map_natCast]
        exact Ideal.absNorm_mem _
      have h3 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 B.fields.F) ∈
          Ideal.comap (algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E)) P.asIdeal := h2
      rw [Ideal.mem_comap, map_natCast] at h3
      exact h3
    have hQ0 : Ideal.absNorm Q.asIdeal ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have hN : Nat.card (kP P) ≠ 0 := by
      have hP0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hP0
    have hmem : rootN (Nat.card (kP P)) ∈ GlobalTheory.Mem.Col2.RootsIn.Sv B.toPre (Set.range I.xi) := by
      unfold GlobalTheory.Mem.Col2.RootsIn.Sv
      refine Finset.mem_biUnion.2 ⟨I.xi a, (mem_finOr (Set.finite_range _)).2 ⟨a, rfl⟩, ?_⟩
      unfold rootsOf
      refine Finset.mem_biUnion.2 ⟨Q, (mem_finOr (ramSet_finite _)).2 hQ, ?_⟩
      exact Finset.mem_image.2 ⟨P, (mem_finOr (overN_finite hQ0)).2 hQP, rfl⟩
    obtain ⟨z, hz⟩ := (B.mem_LLC).1 (hS _ hmem)
    refine ⟨z, IsPrimitiveRoot.of_map_of_injective (f := B.embLL) ?_ B.embLL.injective⟩
    rw [hz]
    exact Complex.isPrimitiveRoot_exp _ hN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfBases
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
open scoped ComplexOrder

namespace GlobalTheory.Mem.ColTie

section Lin

variable {K M : Type} [Field K] [AddCommGroup M] [Module ℂ M] {σ : K →+* ℂ} {n : ℕ}

theorem eq_sum_single (x : Fin n → K) : x = ∑ i, x i • (Pi.single i (1 : K) : Fin n → K) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem mem_span_single (j : (Fin n → K) →ₛₗ[σ] M) (x : Fin n → K) :
    j x ∈ Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_single x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem span_single_eq (j : (Fin n → K) →ₛₗ[σ] M) :
    Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = Submodule.span ℂ (Set.range j) := by
  refine le_antisymm (Submodule.span_mono ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact mem_span_single j x

theorem exists_equiv_of_bases {M' : Type} [AddCommGroup M'] [Module ℂ M'] (j : (Fin n → K) →ₛₗ[σ] M)
    (j' : (Fin n → K) →ₛₗ[σ] M') (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤)
    (hli' : LinearIndependent ℂ fun i => j' (Pi.single i 1))
    (hsp' : Submodule.span ℂ (Set.range fun i => j' (Pi.single i 1)) = ⊤) :
    ∃ e : M ≃ₗ[ℂ] M', ∀ x, e (j x) = j' x := by
  let b := Module.Basis.mk hli hsp.ge
  let b' := Module.Basis.mk hli' hsp'.ge
  refine ⟨b.equiv b' (Equiv.refl _), fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_single x, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ j, map_smulₛₗ j', LinearEquiv.map_smul]
  congr 1
  have h1 : j (Pi.single i 1) = b i := (Module.Basis.mk_apply hli hsp.ge i).symm
  have h2 : j' (Pi.single i 1) = b' i := (Module.Basis.mk_apply hli' hsp'.ge i).symm
  rw [h1, h2, Module.Basis.equiv_apply, Equiv.refl_apply]

end Lin

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

def ipLev (z z' : MtildeV W Ch sel mu P) : X.K :=
  (mtildeGSD W Ch sel mu P).ip (mtildeOk W Ch sel mu hX P) z.1 z'.1

def ipK (z z' : MtildeV W Ch sel mu P) : X.K :=
  (mtildeKGSD W Ch sel mu).ip (mtildeKOk W Ch sel mu hX) z.1 z'.1

theorem li_zOf : LinearIndependent X.K fun i => zOf W Ch sel mu P hX (Pi.single i 1) := by
  have h := (Pi.basisFun X.K (Fin (dimP W Ch sel mu P hX))).linearIndependent.map' (zOf W Ch sel mu P hX)
    (LinearMap.ker_eq_bot.2 (zOf_injective W Ch sel mu P hX))
  simpa [Function.comp_def] using h

def jP (σ : X.K →+* ℂ) : (Fin (dimP W Ch sel mu P hX) → X.K) →ₛₗ[σ] MtP W Ch sel mu P σ :=
  (toMtP W Ch sel mu P σ).comp (zOf W Ch sel mu P hX)

theorem linearIndependent_jP_single (σ : X.K →+* ℂ) : LinearIndependent ℂ fun i => jP W Ch sel mu P hX σ (Pi.single i 1) :=
  toMtilde_linearIndependent W Ch sel mu P σ (li_zOf W Ch sel mu P hX)

theorem span_range_jP_single_eq_top (σ : X.K →+* ℂ) : Submodule.span ℂ (Set.range fun i => jP W Ch sel mu P hX σ (Pi.single i 1)) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← toMtilde_span W Ch sel mu P σ hX, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  obtain ⟨x, rfl⟩ := zOf_surjective W Ch sel mu P hX z
  exact mem_span_single (jP W Ch sel mu P hX σ) x

end Gen

section TC

attribute [local instance] starE

def sig (B : Base) : B.fields.K →+* ℂ := B.embLL

end TC

end GlobalTheory.Mem.ColTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupIdentificationFixedPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3

theorem exists_grpIdent : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → GrpAt X I → LevOf X I U L → ∃ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), IsPlacewiseIdentity X (px := px) eG ∧ (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧ (∀ kv, L.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv) := by
  intro X px I U L hI hG hL
  obtain ⟨plg0, hplg0⟩ := hG.pl
  have hPr := (base_fields_primes_ok X.B px).2.1
  have h1 : ∀ P, P ∈ L.Pg ↔ P ∈ (X.B.primes px).vGs := fun P => by rw [hL.Pg]; exact Iff.rfl
  let eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r :=
    { toFun := fun g PP => g ⟨PP.1, (h1 _).1 PP.2⟩
      invFun := fun h PP => h ⟨PP.1, (h1 _).2 PP.2⟩
      left_inv := fun g => rfl
      right_inv := fun h => rfl
      map_mul' := fun _ _ => rfl }
  let plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg := plg0.trans (Equiv.subtypeEquivRight fun P => (h1 P).symm)
  have hmem : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ((plg kv : L.Pg) : Pl X.toD7.host.E) ∈ (X.B.primes px).vG kv.1 :=
    fun kv => (hI.pibar kv.1 _).2 (hplg0 kv).2
  have hiso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), Nonempty (ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1) := by
    intro kv
    haveI : Fact (X.toD7.host.g kv.1).Prime := ⟨hPr.g_prime kv.1⟩
    obtain ⟨e⟩ := Formalism.L2.Col.residueField_equiv_zmod (X := X.B.fields) (plg kv).1 (X.toD7.host.g kv.1) (hPr.vG_norm kv.1 _ (hmem kv))
    exact ⟨e.symm⟩
  let iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1 := fun kv => Classical.choice (hiso kv)
  let cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd :=
    { toEquiv := (Equiv.piCongrLeft (fun PP : L.Pg => GL (Fin X.toD7.R.r) (kP PP.1)) plg).symm.trans
        (Equiv.piCongrRight fun kv => (Formalism.L2.Col.generalLinearEquivOfRingEquiv X.toD7.R.r (iso kv).symm).toEquiv)
      map_mul' := fun f f' => by
        funext kv
        exact map_mul (Formalism.L2.Col.generalLinearEquivOfRingEquiv X.toD7.R.r (iso kv).symm) (f (plg kv)) (f' (plg kv)) }
  refine ⟨eG, cG, plg, iso, fun g P h h' => rfl, fun kv => (hplg0 kv).1, fun kv => ?_, fun g kv => ?_⟩
  · rw [hL.C]
    exact (hplg0 kv).2
  · show _ = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1)
      (Formalism.L2.Col.generalLinearEquivOfRingEquiv X.toD7.R.r (iso kv).symm (eG g (plg kv)))
    ext i j
    simp [Formalism.UG.bc, Formalism.L2.Col.generalLinearEquivOfRingEquiv]
end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedIntegralOfSeparatingElement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem valuation_le_one_of_valuation_one_sub_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {a : Ω} (ha : A.valuation (1 - a) < 1) : A.valuation a ≤ 1 := by
  have e : a = 1 - (1 - a) := by ring
  rw [e]
  refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ha.le)
  rw [map_one]

theorem valuation_one_sub_mul_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω}
    (ha : A.valuation (1 - a) < 1) (hb : A.valuation (1 - b) < 1) :
    A.valuation (1 - a * b) < 1 := by
  have e : 1 - a * b = (1 - a) + a * (1 - b) := by ring
  rw [e]
  refine Valuation.map_add_lt _ ha ?_
  rw [map_mul]
  calc A.valuation a * A.valuation (1 - b) ≤ 1 * A.valuation (1 - b) :=
        by gcongr; exact valuation_le_one_of_valuation_one_sub_lt A ha
    _ = A.valuation (1 - b) := one_mul _
    _ < 1 := hb

theorem exists_fixed_of_separating :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (σ : G E Ω), σ ∈ Ine (F := E) A' → ∀ (e₀ c : Ω), IsIntegral ℤ e₀ → A.valuation e₀ < A.valuation c → A'.valuation (1 - e₀) < 1 → ∃ e : Ω, IsIntegral ℤ e ∧ σ e = e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  intro E Ω _ _ _ _ _ A A' σ hσ e₀ c hint hA hA'
  obtain ⟨k, hk, hfix⟩ := galAlgClosure_exists_pos_pow_apply_eq E Ω σ e₀
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set f : ℕ → Ω := fun i => (σ ^ i) e₀ with hf
  have hfint : ∀ i, IsIntegral ℤ (f i) := fun i =>
    hint.map ((σ ^ i : Ω ≃ₐ[E] Ω).toRingEquiv.toRingHom.toIntAlgHom)
  have hshift : ∀ i, σ (f i) = f (i + 1) := by
    intro i
    simp only [hf, pow_succ', AlgEquiv.mul_apply]

  have hcong : ∀ i, A'.valuation (1 - f i) < 1 := by
    intro i
    induction i with
    | zero => simpa [hf] using hA'
    | succ i ih =>
      have hy : A'.valuation (f i) ≤ 1 := valuation_le_one_of_valuation_one_sub_lt A' ih
      have hmove := hσ.2 (f i) hy
      have e : 1 - f (i + 1) = (1 - f i) + -(σ (f i) - f i) := by
        rw [← hshift i]; ring
      rw [e]
      refine Valuation.map_add_lt _ ih ?_
      rw [Valuation.map_neg]
      exact hmove
  refine ⟨∏ i ∈ Finset.range (m + 1), f i, ?_, ?_, ?_, ?_⟩
  · exact IsIntegral.prod _ (fun i _ => hfint i)
  · rw [map_prod]
    simp only [hshift]
    rw [Finset.prod_range_succ (fun i => f (i + 1)), Finset.prod_range_succ' f]
    have h0 : f (m + 1) = f 0 := by simpa [hf] using hfix
    rw [h0]
  · rw [Finset.prod_range_succ']
    have hP : IsIntegral ℤ (∏ i ∈ Finset.range m, f (i + 1)) :=
      IsIntegral.prod _ (fun i _ => hfint (i + 1))
    have hPle : A.valuation (∏ i ∈ Finset.range m, f (i + 1)) ≤ 1 :=
      (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A hP)
    rw [map_mul]
    calc A.valuation (∏ i ∈ Finset.range m, f (i + 1)) * A.valuation (f 0)
        ≤ 1 * A.valuation (f 0) := by gcongr
      _ = A.valuation e₀ := by simp [hf]
      _ < A.valuation c := hA
  · refine Finset.prod_induction f (fun x => A'.valuation (1 - x) < 1)
      (fun a b ha hb => valuation_one_sub_mul_lt A' ha hb) ?_ (fun i _ => hcong i)
    simp

end GlobalTheory
end

