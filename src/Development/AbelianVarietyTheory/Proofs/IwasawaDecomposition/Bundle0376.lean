module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0009
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Formalism.LocalToGlobal.Columns.Bundle0013
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharSymMulInvEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0136
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Formalism.LocalToGlobal.Columns.AdelicLemmas

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceFixedVectorSumSphericalImages
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SphAvg

open GlobalTheory.SplitWeil

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem exists_lift {n : ℕ} (s : SplitPlace L)
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hi : Continuous i)
    (y : GL (Fin n) (s.w.adicCompletion L)) (hy : y ∈ KO (s.w.adicCompletion L) (Fin n)) :
    ∃ κ : GAf L n, κ ∈ Umax L n ∧ TrivOutside {s.v} κ ∧
      Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n κ) = y := by
  have hE := GlobalTheory.ConjParahoric.isEquiv_of_continuous i hi
  have hle : ∀ x, ValuativeRel.valuation (s.w.adicCompletion L) x ≤ 1 → Valued.v (i.symm x) ≤ 1 :=
    fun x hx => (Valuation.isEquiv_iff_val_le_one.1 hE).2 hx
  obtain ⟨u, rfl⟩ := hy
  set M := Matrix.GeneralLinearGroup.map i.symm.toRingHom
    (Matrix.GeneralLinearGroup.map (algebraMap _ (s.w.adicCompletion L)) u) with hM
  obtain ⟨κ, hκ, hloc⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s M
  have mem_Umax_of_loc (s : SplitPlace L) (x : GAf L n) (hx : TrivOutside {s.v} x)
      (h1 : ∀ i j, Valued.v (((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) ≤ 1)
      (h2 : ∀ i j, Valued.v (((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) ≤ 1) :
      x ∈ Umax L n := by
    obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
    intro i j
    have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
        (((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
      rw [GlobalTheory.FinTypCount.inv_val]
      rfl
    have hz : (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
      apply GlobalTheory.mem_ALint_of_supported_at_split L s e he he'
      · intro w hw
        have := congrFun (congrFun (hx w (by simpa using hw)) i) j
        simp only [Matrix.map_apply] at this
        rw [map_sub, this]
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      · have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
            ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := rfl
        rw [map_sub, e1]
        refine (Valuation.map_sub _ _ _).trans (max_le (h1 i j) ?_)
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      · have e1 : s.proj ((((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
            ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i := rfl
        rw [map_sub, map_sub, hconj, e1]
        refine (Valuation.map_sub _ _ _).trans (max_le (h2 j i) ?_)
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have := add_mem hz (show (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])
    simpa using this
  refine ⟨κ, mem_Umax_of_loc s κ hκ ?_ ?_, hκ, ?_⟩
  · intro a b
    rw [hloc]
    exact hle _ (u.val a b).2
  · intro a b
    rw [map_inv, hloc, hM, ← map_inv, ← map_inv]
    exact hle _ ((u⁻¹).val a b).2
  · rw [hloc, hM]
    ext a b
    simp

theorem exists_fixed_of_sum {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hi : Continuous i)
    {ι : Type} [Fintype ι] (T : ι → σ.V →ₗ[ℂ] (GAf L n → W))
    (hT : ∀ j, GlobalTheory.HeckeFrob.IsLocMap s σ i (T j)) (u : ι → σ.V) (f : GAf L n → W)
    (hf : f = ∑ j, T j (u j)) (hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) :
    ∃ e : ι → σ.V, (∀ j, e j ∈ GlobalTheory.PRep.fixed σ.ρ (KO (s.w.adicCompletion L) (Fin n))) ∧
      f = ∑ j, T j (e j) := by
  classical
  let H : Subgroup (GL (Fin n) (s.w.adicCompletion L)) :=
    { carrier := {g | ∀ j, σ.ρ g (u j) = u j}
      mul_mem' := fun {a b} ha hb j => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb j, ha j]
      one_mem' := fun j => by simp
      inv_mem' := fun {a} ha j => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        conv_lhs => rw [← ha j]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hHo : IsOpen (H : Set (GL (Fin n) (s.w.adicCompletion L))) := by
    have : (H : Set (GL (Fin n) (s.w.adicCompletion L))) = ⋂ j, {g | σ.ρ g (u j) = u j} := by
      ext g; simp [H]
    rw [this]
    exact isOpen_iInter_of_finite fun j => σ.smooth (u j)
  set K := KO (s.w.adicCompletion L) (Fin n) with hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp GlobalTheory.SplitFlip.isCompact_KO
  haveI : Finite (K ⧸ H.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hHo.preimage continuous_subtype_val)
  letI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  set N : ℂ := (Fintype.card (K ⧸ H.subgroupOf K) : ℂ) with hNdef
  have hN : N ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let e : ι → σ.V := fun j => N⁻¹ • ∑ q : K ⧸ H.subgroupOf K, σ.ρ ((q.out : K) : GL (Fin n) _) (u j)
  refine ⟨e, fun j => ?_, ?_⟩
  · intro k
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, map_smul, map_sum]
    congr 1
    have hstep : ∀ q : K ⧸ H.subgroupOf K, σ.ρ (k : GL (Fin n) _) (σ.ρ ((q.out : K) : GL (Fin n) _) (u j)) =
        σ.ρ (((k • q).out : K) : GL (Fin n) _) (u j) := by
      intro q
      have hq : (QuotientGroup.mk ((k • q).out) : K ⧸ H.subgroupOf K) = QuotientGroup.mk (k * q.out) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have hmem := QuotientGroup.eq.1 hq
      rw [Subgroup.mem_subgroupOf] at hmem
      have h1 : ((k * q.out : K) : GL (Fin n) (s.w.adicCompletion L)) =
          (((k • q).out : K) : GL (Fin n) (s.w.adicCompletion L)) *
            ((((k • q).out)⁻¹ * (k * q.out) : K) : GL (Fin n) (s.w.adicCompletion L)) := by
        rw [← Subgroup.coe_mul, mul_inv_cancel_left]
      rw [← Module.End.mul_apply, ← map_mul]
      change σ.ρ ((k * q.out : K) : GL (Fin n) _) (u j) = _
      rw [h1, map_mul, Module.End.mul_apply, hmem j]
    simp_rw [hstep]
    exact Equiv.sum_comp (MulAction.toPerm k) (fun (q : K ⧸ H.subgroupOf K) => σ.ρ ((q.out : K) : GL (Fin n) (s.w.adicCompletion L)) (u j))
  · choose κ hκU hκT hκ using fun (q : K ⧸ H.subgroupOf K) => exists_lift s i hi ((q.out : K) : GL (Fin n) _) q.out.2
    have key : ∀ q : K ⧸ H.subgroupOf K, ∑ j, T j (σ.ρ ((q.out : K) : GL (Fin n) _) (u j)) = f := by
      intro q
      rw [← hκ q]
      simp_rw [hT _ (κ q) (hκT q)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← hf, hfix _ (hκU q) (hκT q)]
    calc f = N⁻¹ • ∑ _q : K ⧸ H.subgroupOf K, f := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← hNdef,
            inv_mul_cancel₀ hN, one_smul]
      _ = N⁻¹ • ∑ q : K ⧸ H.subgroupOf K, ∑ j, T j (σ.ρ ((q.out : K) : GL (Fin n) _) (u j)) := by
          simp_rw [key]
      _ = ∑ j, T j (e j) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [e, map_smul, map_sum, ← Finset.smul_sum]
          rw [Finset.sum_comm]

end GlobalTheory.SphAvg

namespace GlobalTheory.SphAvg

theorem exists_sum_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i →
    (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) →
    ∀ f, f ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 →
    (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
    ∃ (m : ℕ) (T : Fin m → σ.V →ₗ[ℂ] (GAf L n → π.W)) (e : Fin m → σ.V),
      (∀ j, GlobalTheory.HeckeFrob.IsLocMap s σ i (T j)) ∧
      (∀ j, e j ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n))) ∧ f = ∑ j, T j (e j) := by
  intro L _ _ _ n π s σ i hi _ f hf hfix
  classical
  obtain ⟨c, hc, hcf⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).1 hf
  choose u hu using hc
  have hsum : f = ∑ t : c.support, t.1.1 (u t.1) := by
    rw [← hcf, Finsupp.sum, ← Finset.sum_coe_sort]
    exact Finset.sum_congr rfl fun t _ => (hu t.1).symm
  obtain ⟨e, he, hfe⟩ := exists_fixed_of_sum s σ i hi (ι := c.support) (fun t => t.1.1)
    (fun t => t.1.2.2) (fun t => u t.1) f hsum hfix
  · refine ⟨c.support.card, fun j => (c.support.equivFin.symm j).1.1,
      fun j => e (c.support.equivFin.symm j), fun j => (c.support.equivFin.symm j).1.2.2,
      fun j => he _, ?_⟩
    rw [hfe]
    exact (Equiv.sum_comp c.support.equivFin.symm (fun t => t.1.1 (e t))).symm

end GlobalTheory.SphAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportedAtConjPrimeIdempotentOfTrivialOffPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section

namespace GlobalTheory.Mem.SuppOffPlace

section Gen

variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]

theorem prV_entry_eq_zero {n : ℕ} (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (w : HeightOneSpectrum (𝓞 F))
    (h : Formalism.UG.bc (Formalism.UG.prV (E := E) w) g = 1) (i j : Fin n) : Formalism.UG.prV (E := E) w ((g.val - 1) i j) = 0 := by
  have h1 : (Formalism.UG.bc (Formalism.UG.prV (E := E) w) g).val i j = (1 : GL (Fin n) (E ⊗[F] w.adicCompletion F)).val i j := by
    rw [h]
  rw [Formalism.UG.bc, Units.coe_map] at h1
  change Formalism.UG.prV (E := E) w (g.val i j) = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] w.adicCompletion F)) i j at h1
  rw [Matrix.sub_apply, map_sub, h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem eps_mul_of_off (v : HeightOneSpectrum (𝓞 F)) {y : E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hy : ∀ w, w ≠ v → Formalism.UG.prV (E := E) w y = 0) : Formalism.UG.P.afsplitEps E v * y = y := by
  rw [← sub_eq_zero]
  apply Formalism.UG.P.afsplit_inj
  intro w
  rw [map_sub, map_mul]
  by_cases h : w = v
  · subst h
    rw [Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]
  · rw [hy w h, mul_zero, sub_zero]

end Gen

variable {D : D7}

theorem belowPl_conjP {v : HeightOneSpectrum (𝓞 D.host.F)} {Pb : Formalism.L2.DIV.Pl D.host.E}
    (h : Formalism.L2.Col.IsOver v Pb) : Formalism.IndefR.Fin.belowPl (D := D) (Formalism.L2.Col.conjPrime₂ Pb) = v := by
  apply HeightOneSpectrum.ext
  rw [h]
  ext x
  show Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ∈ Pb.asIdeal ↔
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ Pb.asIdeal
  have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    apply RingOfIntegers.ext
    show star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = _
    rw [show ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) from rfl]
    exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  rw [this]

theorem afsplitI_one (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Formalism.UG.P.afsplitI v (1 : v.adicCompletion D.host.F) = Formalism.IndefR.Fin.sglV v 1 := by
  apply Formalism.IndefR.Fin.af_ext
  intro w
  by_cases hw : w = v
  · subst hw
    rw [Formalism.IndefR.Fin.sglV_same]
    exact Formalism.UG.P.afsplitI_self w 1
  · rw [Formalism.IndefR.Fin.sglV_ne v _ hw]
    exact Formalism.UG.P.afsplitI_ne v w hw 1

theorem swap_finPart_phiE (v : HeightOneSpectrum (𝓞 D.host.F)) :
    swapAE D (finPart D (Formalism.IndefR.Fin.phiE v 1)) = Formalism.UG.P.afsplitEps D.host.E v := by
  rw [Formalism.UG.P.afsplitEps, Algebra.TensorProduct.one_def, Formalism.UG.P.afsplitIE_tmul, afsplitI_one]
  rfl

theorem suppAt_of_trivial_off : ∀ {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → ∀ α : GA D V, α ∈ GfC V → (∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (finE V α) = 1) → SuppAt e V α := by
  intro D V v Pb e hO hI α hα hw
  rw [GlobalTheory.HeckeTrans.suppAt_iff e hα, Formalism.IndefR.Fin.below_of_idemAt hI, belowPl_conjP hO,
    ← GlobalTheory.HeckeTrans.finE_unswap]
  have hM : (finE V α).val.map
      (GlobalTheory.HeckeTrans.unswap D) - 1 =
      ((finE V α).val - 1).map
      (GlobalTheory.HeckeTrans.unswap D) := by
    rw [Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  rw [hM]
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
  apply Function.LeftInverse.injective (GlobalTheory.HeckeTrans.unswap_swap (D := D))
  rw [map_mul, swap_finPart_phiE, GlobalTheory.HeckeTrans.swap_unswap]
  exact eps_mul_of_off v (fun w hw' => prV_entry_eq_zero _ w (hw w hw') i j)

end GlobalTheory.Mem.SuppOffPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricLevelBoundLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.LastGrp

open GlobalTheory.SymLevelInv LocE Loc

theorem posSym_eq_symIdx (k rS x : ℕ) : posSym k rS x = symIdx k rS x := by
  unfold posSym symIdx
  split_ifs <;> omega

theorem symmetric_level_bound_le (k rS s : ℕ) : bd5 k rS s ≤ s := by
  unfold bd5
  split_ifs <;> omega

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem inJSym_of_mat (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k rS r t n : ℕ} (hr : r = rSym k rS) (ht : 0 < t) (hn : r ≤ n)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k rS r t n 0) {κ : Type} [Field κ]
    (e : (𝓞 E ⧸ P.asIdeal) →+* κ) (M : Matrix (Fin n) (Fin n) κ) (hM : ∀ i j : Fin n, M i j = e (redP P (mat g i j))) :
    InJSym k rS t false M := by
  subst hr
  have hr' : k + rS < rSym k rS := by
    unfold rSym
    omega
  refine ⟨fun x y h => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun h => by simp at h⟩
  · have hxy : x.1 ≠ y.1 := fun h' => by rw [h'] at h; omega
    by_cases hy : y.1 < rSym k rS
    · have key : bd5 k rS (symIdx k rS y.1) ≤ symIdx k rS x.1 := by
        refine (symmetric_level_bound_le _ _ _).trans ?_
        rw [lvSym_of_lt hy, posSym_eq_symIdx] at h
        by_cases hx : x.1 < rSym k rS
        · rw [lvSym_of_lt hx, posSym_eq_symIdx] at h
          exact h.le
        · have h1 := symIdx_lt hr'.le hy
          have h2 := symIdx_cases k rS x.1
          omega
      rw [hM, mat_col hq hP hr' hn hg x.1 y.1 x.2 hy key, if_neg hxy, map_zero]
    · have hx : ¬ x.1 < rSym k rS := by
        intro hx
        have h1 := lvSym_of_ge (t := t) hy
        rw [lvSym_of_lt hx] at h
        have h2 := posSym_lt hx
        omega
      unfold lvSym at h
      rw [if_neg hy, if_neg hx] at h
      have h1 : (y.1 - rSym k rS) / t + 1 ≤ (x.1 - rSym k rS) / t := by omega
      have h2 := Nat.lt_mul_div_succ (y.1 - rSym k rS) ht
      have h3 := Nat.div_mul_le_self (x.1 - rSym k rS) t
      have h4 := Nat.mul_le_mul_right t h1
      rw [mul_comm] at h2
      rw [hM, mat_blk hq hP hr' hg ((y.1 - rSym k rS) / t + 1) x.1 y.1 x.2 (by omega) (by omega), map_zero]
  · rw [hM, mat_col hq hP hr' hn hg x.1 x.1 x.2 hx (symmetric_level_bound_le _ _ _), if_pos rfl, map_one]
  · have hyr : y.1 < rSym k rS := by omega
    have key : bd5 k rS (symIdx k rS y.1) ≤ symIdx k rS x.1 := by
      rw [hy]
      unfold bd5 symIdx
      split_ifs <;> omega
    rw [hM, mat_col hq hP hr' hn hg x.1 y.1 x.2 hyr key, if_neg (by omega), map_zero]

theorem inJSym_of_prX (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k rS r t n c : ℕ} (hc : c = 0) (hr : r = rSym k rS) (ht : 0 < t)
    (hn : r ≤ n) {ρ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hρ : ρ ∈ JGsym P q k rS r t n c) {g : Sp E n ≃ₗ[E] Sp E n}
    (hx : ∀ x, ρ (Loc.inX E n c x) = Loc.inX E n c (g x)) {κ : Type} [Field κ] (e : (𝓞 E ⧸ P.asIdeal) →+* κ)
    (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) (hM : ∀ x ∈ stdAt E n P, redV P (g x) = M.mulVec (redV P x)) :
    InJSym k rS t false (M.map e) := by
  subst hc
  refine inJSym_of_mat hq hP hr ht hn hρ e _ fun i j => ?_
  have h6 := congrFun (hM _ (TopStep.single_mem_stdAt j)) i
  rw [TopStep.redV_single, Matrix.mulVec_single_one] at h6
  have h7 : mat ρ i.1 j.1 = g (Pi.single j 1) i := by
    have h8 : eN E (n + 0) j.1 = Loc.inX E n 0 (Pi.single j 1) := by
      funext l
      rw [CongLevel.inX_apply, dite_eq_left (show l.1 < n from l.2)]
      unfold Loc.eN
      simp [Pi.single_apply, Fin.ext_iff]
    unfold mat atN
    rw [dite_eq_left (show i.1 < n + 0 from i.2), h8, hx, CongLevel.inX_apply, dite_eq_left i.2]
  rw [Matrix.map_apply, h7]
  exact congrArg e h6.symm

end GlobalTheory.Mem.LastGrp

theorem GlobalTheory.Mem.LastGrp.levG_le_JSymG : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ∀ (j : ℕ), j + 1 = R.m → ∀ (b : L.β j) (w : {w // w ∈ Pr.vGs}) (κ : Type) [Field κ] (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* κ) (M : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)), M ∈ (L.levG j b w).H → Matrix.GeneralLinearGroup.map e.toRingHom M ∈ JSymG κ (R.N j) R.k (rSD R) R.t false := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hSel hL hs j hj b w κ _ e M hM
  letI : StarRing X.E := X.starE
  have hm := hL.hm
  obtain rfl : j = m2 + 1 := by omega
  have hc : cOf R (m2 + 1) = 0 := by
    unfold cOf
    omega
  have hq : qOf w.1 ≠ 0 := fun h => TopStep.qOf_ne_zero (P := w.1) (by rw [h]; simp)
  have hP : ((qOf w.1 : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal := Ideal.absNorm_mem _
  have hr : R.r = rSym R.k (rSD R) := by
    obtain ⟨a, ha⟩ := R.m_even
    unfold Ranks.r rSym rSD
    omega
  have ht : 0 < R.t := by
    have := R.three_m_lt_t
    omega
  have hn : R.r ≤ R.N (m2 + 1) := by
    unfold Ranks.r Ranks.N
    rw [mul_add, mul_one]
    omega
  have key : ∀ A : GL (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal), A ∈ (L.levG (m2 + 1) b w).H →
      InJSym R.k (rSD R) R.t false ((A.1).map e.toRingHom) := by
    intro A hA
    obtain ⟨g, hg, hred⟩ := (hL.grpG _ b w A).1 hA
    unfold prCat at hg
    rw [hL.last_h] at hg
    obtain ⟨ρ, hρ, hx⟩ := hg
    have hJ : ρ ∈ Jat (Pr := Pr) cst.sharp (m2 + 1) w.1 := by simpa [Loc.Cbe] using hρ.2
    unfold Jat at hJ
    rw [if_pos w.2, if_pos hs] at hJ
    exact inJSym_of_prX hq hP hc hr ht hn hJ hx e.toRingHom A.1 hred
  refine ⟨key M hM, ?_⟩
  rw [← map_inv]
  exact key _ (inv_mem hM)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeEqDecoratedLatticeReindexed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.R3.LiftLatStd

theorem hLat_eq_decoPt_N : ∀ (X : Stages) (i : Fin X.toD7.R.m) (Λ : Submodule (𝓞 X.toD7.host.E) (Fin (Vc X.toD7 i).rank → X.toD7.host.E)),
    IsSDFrame (Vc X.toD7 i) 1 Λ 1 → ∀ (SG : Finset (Pl X.toD7.host.E))
    (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i)),
    (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) →
    ∀ x : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV,
      Bridge.hLat (Vc X.toD7 i) (eG x) =
        (Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ SG (QuotientGroup.mk x)).1.N.map
          (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (LiftBrg.rkEq X i)).symm).toLinearMap := by
  intro X i Λ hΛ SG eG hx x
  have hΛ' := hΛ
  obtain ⟨c, hfr, -⟩ := hΛ'
  rw [GlobalTheory.HLatMove.hLat_eq_span hΛ, Formalism.L2.Col.decoPt_mk]
  unfold Formalism.L2.Col.decoOf
  rw [dite_eq_left (Formalism.L2.Col.decorated_lattice_exists _ _ _ _ _ x.2)]
  set h := eG x with hh
  set g := Formalism.UG.bc (swapAE X.toD7) (h : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E)) with hg
  have hxg : (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) = LiftBrg.castGL (LiftBrg.rkEq X i).symm g := (hx x).symm
  have hL : ∀ y : Fin (Vc X.toD7 i).rank → X.toD7.host.E,
      (h.1⁻¹).1 *ᵥ (fun j => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F) ⊗ₜ[X.toD7.host.F] y j) ∈
          GlobalTheory.AdLat.hat X.toD7.host.F (Λ : Set (Fin (Vc X.toD7 i).rank → X.toD7.host.E)) ↔
        ∀ j, ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) j ∈
          Formalism.L2.Herm.intAf X.toD7.host.F X.toD7.host.E := by
    intro y
    have e : ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) =
        fun j => Algebra.TensorProduct.comm X.toD7.host.F _ X.toD7.host.E
          (((h.1⁻¹).1 *ᵥ (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F) ⊗ₜ[X.toD7.host.F] y k)) j) := by
      rw [hg, ← map_inv]
      funext j
      change _ = swapAE X.toD7 _
      rw [RingHom.map_mulVec (swapAE X.toD7)]
      rfl
    have e1 := hfr ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k)))
    rw [inv_one, Units.val_one, Matrix.one_mulVec] at e1
    rw [← e1, e]
    constructor
    · intro hz
      exact GlobalTheory.PrincInLevel.swap_mem_hatL Λ _ hz
    · intro hz
      have := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ hz
      simpa only [AlgEquiv.symm_apply_apply] using this
  have hR : ∀ y : Fin (Vc X.toD7 i).rank → X.toD7.host.E,
      y ∈ (Formalism.UG.CS.globLat (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (Formalism.L2.Col.stdLat X.toD7.host.E X.B.R.nV)).map
          (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (LiftBrg.rkEq X i)).symm).toLinearMap ↔
        ∀ j, ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) j ∈
          Formalism.L2.Herm.intAf X.toD7.host.F X.toD7.host.E := by
    intro y
    rw [Submodule.mem_map_equiv, LinearEquiv.funCongrLeft_symm, Formalism.L2.Col.mem_globLat]
    unfold Formalism.L2.Col.pullV
    rw [hxg, ← map_inv]
    simp only [LiftBrg.castGL, Units.coe_mapEquiv, Equiv.symm_symm, LinearEquiv.funCongrLeft_apply]
    simp only [LinearMap.funLeft_apply]
    have e2 : ∀ (M : Matrix (Fin (Vc X.toD7 i).rank) (Fin (Vc X.toD7 i).rank) (Lev.EAf X.toD7)),
        ((Matrix.reindexAlgEquiv (Lev.EAf X.toD7) (Lev.EAf X.toD7) (finCongr (LiftBrg.rkEq X i).symm)).toRingEquiv.toMulEquiv M) *ᵥ
          (fun a => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y (finCongr (LiftBrg.rkEq X i) a))) =
        fun a => (M *ᵥ fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k)) (finCongr (LiftBrg.rkEq X i) a) := by
      intro M
      change Matrix.reindexAlgEquiv (Lev.EAf X.toD7) (Lev.EAf X.toD7) (finCongr (LiftBrg.rkEq X i).symm) M *ᵥ _ = _
      rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
      funext a
      simp [Function.comp_def]
    rw [e2]
    exact ⟨fun H j => by simpa using H ((finCongr (LiftBrg.rkEq X i)).symm j), fun H a => H _⟩
  refine le_antisymm (Submodule.span_le.2 fun y hy => (hR y).2 ((hL y).1 hy)) fun y hy => Submodule.subset_span ((hL y).2 ((hR y).1 hy))

end GlobalTheory.Mem.R3.LiftLatStd
end

