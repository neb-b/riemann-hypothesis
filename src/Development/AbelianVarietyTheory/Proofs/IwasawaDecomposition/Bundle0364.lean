module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Formalism.LocalToGlobal.UnitaryNorms.DatumS
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0358

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.DatCopy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def setIo (R : RealDat3 D A Ks) (y : type_of% R.ioY) (x : type_of% R.ioX) : RealDat3 D A Ks :=
  { R with ioY := y, ioX := x }

end Gen

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Three

set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false

variable {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) {F : Face3 a.D A}

def twice : RealDat3 a.D A Ks := (by with_unfolding_all exact ((real3 (a := b) a (iK := alg b iK) (real3 b R)) :))

def twiceY : type_of% R.ioY := by
  with_unfolding_all exact ((twice b R).ioY :)

def twiceX : type_of% R.ioX := by
  with_unfolding_all exact ((twice b R).ioX :)

theorem twiceY_eq : R.ioY = twiceY b R := by
  apply eq_of_heq
  with_unfolding_all
    exact (HEq.trans (real_ioY b R.toRealDat)
      (real_ioY (a := b) a (iK := alg b iK) (real b R.toRealDat)) :)

theorem twiceX_eq : R.ioX = twiceX b R := by
  apply eq_of_heq
  with_unfolding_all
    exact (HEq.trans (real_ioX b R.toRealDat)
      (real_ioX (a := b) a (iK := alg b iK) (real b R.toRealDat)) :)

theorem twice_eq : R = twice b R := (by with_unfolding_all exact ((congrArg₂ (setIo R) (twiceY_eq b R) (twiceX_eq b R)) :))

variable {R}

theorem holds_back (h : letI := alg b iK; Holds (real3 b R) (face3 b F)) : Holds R F := by
  have h2 := holds_tr (a := b) a (iK := alg b iK) h
  exact (by with_unfolding_all exact ((cast (congrArg (fun R' : RealDat3 a.D A Ks => Holds R' F) (twice_eq b R).symm) ((h2))) : _))

theorem rowTest_tr (h : Rat.RowTest (R.toCx3 F)) : letI := alg b iK; Rat.RowTest ((real3 b R).toCx3 (face3 b F)) := by
  with_unfolding_all
    exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 => Rat.RowTest X) (toCx3_eq b R F)).mp h :)

end Three

theorem multEq_tr {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} (h : GlobalTheory.CuspMult.MultEq R) :
    letI := alg b iK; GlobalTheory.CuspMult.MultEq (real b R) := by
  intro i M₀ j Φ hI W _ _ σ h1 h2 h3
  have key := h ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact ((ds a M₀) :))) ((by with_unfolding_all exact (j :))) ((by with_unfolding_all exact (Φ :))) ⟨(by with_unfolding_all exact (hI.isom :)), (by with_unfolding_all exact (hI.conj :)), (by with_unfolding_all exact (hI.frame :))⟩ W ((by with_unfolding_all exact (σ :))) ((by with_unfolding_all exact (h1 :))) ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact (h3 :)))
  delta GlobalTheory.CuspMult.cuspMult GlobalTheory.CuspMult.allMaps
  rewrite [mult_eq a b]
  exact (by with_unfolding_all exact (key :))

section Dat

variable {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {Tw : Top.TwDat B} {Wt : Set B.places.Pl}


set_option maxHeartbeats 2000000 in
def copy (s : SameGrp a b) (z : Dat a.st I hX Tw Wt) : Dat b.st I hX Tw Wt :=
  @Dat.mk b.st px I hX Tw Wt z.Xg z.tr (coreJ b z.core) ((by with_unfolding_all exact ((alg b z.alg) :))) ((by with_unfolding_all exact (z.alg_eq :))) ((by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :)))
    ((by with_unfolding_all exact ((z.cG.trans s.iso) :))) ((by with_unfolding_all exact ((geoHalf b (iK := z.alg) z.geo) :))) ((by with_unfolding_all exact ((pins_tr b (iK := z.alg) s z.pins) :)))
    ⟨(by with_unfolding_all exact ((levIs_tr b z.lev.is) :)), (by with_unfolding_all exact ((congrArg (chFr b) z.lev.C) :)), (by with_unfolding_all exact (z.lev.xiH :)), (by with_unfolding_all exact (z.lev.Pg :)), (by with_unfolding_all exact (z.lev.Q :)), (by with_unfolding_all exact (z.lev.beta :))⟩
    ((by with_unfolding_all exact (z.idG :)))
    (by
      have h := (goodSet_iff a.st (px := px) _ _).1 z.good
      have e : ∀ g, a.D.ntypes.e0.coeff ((z.R.eG.trans z.cG) g) = b.D.ntypes.e0.coeff (((z.R.eG.trans z.cG).trans s.iso) g) :=
        fun g => (s.e0 _).symm
      simp only [e] at h
      exact (by with_unfolding_all exact (((goodSet_iff b.st (px := px) ((z.R.eG.trans z.cG).trans s.iso) z.Xg).2 h) :)))
    ((by with_unfolding_all exact (z.mu :))) ((by with_unfolding_all exact (z.fieldValues_mem_fixedField :))) ((by with_unfolding_all exact (z.Ks_le :)))

variable (s : SameGrp a b) {z : Dat a.st I hX Tw Wt}

theorem copy_exAt (h : z.R.toRealDat.ExAt) : (copy b s z).R.toRealDat.ExAt := (by with_unfolding_all exact ((exAt_tr b (iK := z.alg) h) :))

theorem copy_lUnif (h : z.R.toRealDat.LUnif) : (copy b s z).R.toRealDat.LUnif := (by with_unfolding_all exact (h :))

theorem copy_lIntegral (h : z.R.toRealDat.LIntegral) : (copy b s z).R.toRealDat.LIntegral := (by with_unfolding_all exact (h :))

theorem copy_multEq (h : GlobalTheory.CuspMult.MultEq z.R.toRealDat) : GlobalTheory.CuspMult.MultEq (copy b s z).R.toRealDat :=
  (by with_unfolding_all exact ((multEq_tr b (iK := z.alg) h) :))

theorem copy_rowTest (h : Rat.RowTest (z.R.toCx3 z.F)) : Rat.RowTest ((copy b s z).R.toCx3 (copy b s z).F) :=
  (by with_unfolding_all exact ((rowTest_tr b (iK := z.alg) h) :))

theorem holds_of_copy (h : Holds (copy b s z).R (copy b s z).F) : Holds z.R z.F := holds_back b (iK := z.alg) ((by with_unfolding_all exact (h :)))

end Dat

end GlobalTheory.Mem.R3.DatCopy

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetFramesInvariantRationalUnitary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2


open Classical GlobalTheory.TopStep in
theorem cosetIn_smul_unitary : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (j : ℕ), X.Ok → Pr.Ok → ∀ (q q' : PtAt R sel mu cst u j) (γ : UF X.E (R.N j)), q'.1.1 = ((γ, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • q.1.1 → q'.1.2 = (fun z => γ.1 z) '' q.1.2 → cosetIn q' = cosetIn q := by
  intro X Pr R sel S mu cst u j hX hPr q q' γ h1 h2
  funext P
  have key : ∀ y ∈ q.1.2, ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ •
      ((frsF sel mu q'.1.1 P).symm (γ.1 y) - (frsF sel mu q.1.1 P).symm y) ∈ stdAt X.E (R.N j) P.1 := by
    intro y hy
    by_cases hP : P.1 ∈ Pr.vGs
    · rw [if_pos hP, pow_zero, inv_one, one_smul]
      by_cases hj : j + 1 = R.m
      swap
      · have h0 : q.1.2 = ∅ := by
          have := q.2
          rw [ysAt_ys_of_ne sel mu cst hj] at this
          exact this
        rw [h0] at hy
        exact absurd hy (Set.notMem_empty y)
      obtain ⟨y0, hy0, hY⟩ := PtAt.mem_ybSet q hj
      have hy' : y - y0 ∈ locLat (rowSG Pr sel mu) q.1.1.deco.1.N
          (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
        rw [hY] at hy
        exact hy
      have hA : (qOf P.1 : X.E) • y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal q.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy0 P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hB : y - y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal q.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy' P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hx : (qOf P.1 : X.E) • y ∈ q.1.1.deco.1.at P.1 := by
        have e : (qOf P.1 : X.E) • y = (qOf P.1 : X.E) • y0 + (qOf P.1 : X.E) • (y - y0) := by
          rw [← smul_add, add_sub_cancel]
        rw [e]
        exact add_mem hA (smul_mem_locP (intAt_nat _) hB)
      let w : Pr.vGs := ⟨P.1, hP⟩
      have hd : q'.1.1.deco.1 = q.1.1.deco.1.act γ.1 1 := by
        rw [h1]
        rfl
      have hf : IsLiftFr q.1.1.deco.1 w (q.1.1.deco.1.liftFr w) := liftFr_spec q.1.1.deco.2 w
      have hf' : IsLiftFr (q.1.1.deco.1.act γ.1 1) w (q'.1.1.deco.1.liftFr w) := by
        rw [← hd]
        exact liftFr_spec q'.1.1.deco.2 w
      have e1 : frsF sel mu q.1.1 P = q.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dite_eq_left hP]
      have e2 : frsF sel mu q'.1.1 P = q'.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dite_eq_left hP]
      rw [e1, e2]
      let κ := passFr γ.1 1 hf hf'
      have hκ : redGL (R.N j) P.1 κ = 1 := redGL_passFr γ.1 1 hf hf'
      set f := q.1.1.deco.1.liftFr w
      set f' := q'.1.1.deco.1.liftFr w
      have e3 : f'.symm (γ.1 y) = κ.1 (f.symm y) := by
        show _ = f'.symm (γ.1 (f (f.symm y)))
        rw [LinearEquiv.apply_symm_apply]
      rw [e3]
      have hv0 : f.symm ((qOf P.1 : X.E) • y) ∈ stdAt X.E (R.N j) P.1 := by
        rw [← hf.1, LinearEquiv.apply_symm_apply]
        exact hx
      rw [map_smul] at hv0
      have hred := redV_redGL κ hv0
      rw [hκ, Units.val_one, Matrix.one_mulVec] at hred
      have hq := (degOneUnram_of_mem_vGs hX hPr hP).2
      have hq0 : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
      refine mem_stdAt.2 fun i => ?_
      have hi1 := mem_stdAt.1 (glint_mem κ hv0) i
      have hi2 := mem_stdAt.1 hv0 i
      have hr : redP P.1 ((κ.1 ((qOf P.1 : X.E) • f.symm y) - (qOf P.1 : X.E) • f.symm y) i) = 0 := by
        rw [Pi.sub_apply, reduction_sub hi1 hi2, sub_eq_zero]
        exact congrFun hred i
      have := intAt_div_of_redP hq (intAt_sub hi1 hi2) hr
      convert this using 1
      rw [map_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    · rw [if_neg hP]
      have e : (frsF sel mu q'.1.1 P).symm (γ.1 y) = (frsF sel mu q.1.1 P).symm y := by
        rw [LinearEquiv.symm_apply_eq]
        unfold frsF
        rw [dite_eq_right hP, dite_eq_right hP, h1]
        show γ.1 y = γ.1 (q.1.1.fr _ ((((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 ((q.1.1.fr _).symm y)))
        simp
      rw [e, sub_self, smul_zero]
      exact zero_mem _
  ext z
  simp only [cosetIn, Set.mem_setOf_eq]
  rw [h2]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
    refine ⟨y, hy, ?_⟩
    have := add_mem hz (key y hy)
    rwa [← smul_add, sub_add_sub_cancel] at this
  · rintro ⟨y, hy, hz⟩
    refine ⟨γ.1 y, ⟨y, hy, rfl⟩, ?_⟩
    have := sub_mem hz (key y hy)
    rwa [← smul_sub, sub_sub_sub_cancel_right] at this

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLOneEqDual
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (σ : E →+* E)
    (hσ : ∀ x, σ x = star x) (L : Submodule (𝓞 E) (Fin n → E)) :
    dualL σ (1 : Matrix (Fin n) (Fin n) E) L = Formalism.HermitianLatticesTheory.dual (hStd E n) L := by
  have hmem : ∀ y, y ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) L ↔ ∀ x ∈ L, (∑ k, star (x k) * y k) ∈ (algebraMap (𝓞 E) E).range := by
    intro y
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
    rfl
  have hset : dualSet σ (1 : Matrix (Fin n) (Fin n) E) L = (Formalism.HermitianLatticesTheory.dual (hStd E n) L : Set _) := by
    ext y
    rw [SetLike.mem_coe, hmem]
    simp only [dualSet, Set.mem_setOf_eq]
    refine forall₂_congr fun x _ => ?_
    have : hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ k, star (x k) * y k := by
      simp [hform, Matrix.one_apply, hσ]
    rw [this]
  unfold dualL
  rw [hset, Submodule.span_eq]

theorem GlobalTheory.Mem.Col2.TC.ldG_eq_dual_hStd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ (L : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)), LdG (I.rec7 l Z) i hi L = Formalism.HermitianLatticesTheory.dual (hStd B.host.E (B.R.N i)) L := by
  intro B X I hI hP l Z u a i hi L
  have hG : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  unfold LdG
  rw [hG]
  exact GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual _ (fun x => rfl) L

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqPlMapOfConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn.GenOff

theorem mem_iff_of_conj (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) {v : PlE D.host}
    (hc : Formalism.BasicNotions.IsConjPl D.host v s.w) (a : 𝓞 (maximalRealSubfield D.host.E)) :
    algebraMap _ (𝓞 D.host.E) a ∈ v.asIdeal ↔ a ∈ s.v.asIdeal := by
  rw [hc (algebraMap _ (𝓞 D.host.E) a) (algebraMap _ (𝓞 D.host.E) a) ?_, ← Ideal.mem_comap, s.w_under]
  rw [GlobalTheory.SplitPlaceOver.host_conj_eq']
  exact (IsCMField.complexConj_apply_eq_self D.host.E (a : maximalRealSubfield D.host.E)).symm

theorem eq_of_conj (D : D7) {w v u : PlE D.host} (hw : Formalism.BasicNotions.IsConjPl D.host w u) (hv : Formalism.BasicNotions.IsConjPl D.host v u) :
    w = v := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  have hy : ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.SplitPlaceOver.host_conj_eq']
  exact (hw x _ hy).trans (hv x _ hy).symm

theorem eq_plMap_of_conj (D : D7) {v u : PlE D.host} (hc : Formalism.BasicNotions.IsConjPl D.host v u) :
    u = Formalism.L2.Host.CT.plMap GlobalTheory.CMVal.InvConj.conjE v := by
  refine HeightOneSpectrum.ext (Ideal.ext fun z => ?_)
  set x := IsCMField.ringOfIntegersComplexConj D.host.E z
  have hz : z = RingOfIntegers.mapRingEquiv GlobalTheory.CMVal.InvConj.conjE x := by
    apply RingOfIntegers.ext
    show (z : D.host.E) = IsCMField.complexConj D.host.E (x : D.host.E)
    rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.complexConj_apply_apply]
  have hy : (z : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [GlobalTheory.SplitPlaceOver.host_conj_eq', IsCMField.coe_ringOfIntegersComplexConj, IsCMField.complexConj_apply_apply]
  rw [← (hc x z hy), hz, Formalism.L2.Host.CT.mem_plMap]

theorem gen_off_level : ∀ (D : D7) (cf : Formalism.L2.Host.CharFrame D) (l : ℕ) (Q : Finset (PlE D.host)) (ψ : HChar D.host.E), (∀ v, v ∉ Q → ψ.UnrAt v) → ψ.TrivOn D.host.F → ∀ (j : Fin D.R.m) (v : PlE D.host) (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), GenAt D l Q v k → Formalism.BasicNotions.IsConjPl D.host v s.w → s.v ∉ gPl D ∪ qPl D (cf.mu0 j * ((if l = D.host.pde then cf.del' else cf.del) * ψ)) ∧ ¬ s.Above l := by
  intro D cf l Q ψ hψ hT j v k s hg hc
  obtain ⟨-, hvl, hvS, hvQ, -, -⟩ := hg
  have hvn : ∀ n : ℕ, ((n : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal → ((n : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal :=
    fun n h => by
      have := (mem_iff_of_conj D s hc (n : 𝓞 (maximalRealSubfield D.host.E))).2 h
      rwa [map_natCast] at this
  have hoff : ∀ w : PlE D.host, NG.OverPl w s.v → ∀ n : ℕ, ((n : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal →
      ((n : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := fun w hw n h =>
    hvn n (by rw [← hw, Ideal.mem_comap, map_natCast]; exact h)
  have hg' : ∀ w : PlE D.host, NG.OverPl w s.v → ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    intro w hw k hk
    have h := hoff w hw _ hk
    apply hvS
    refine ⟨?_, hvl⟩
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hgPl : s.v ∉ gPl D := by
    rintro ⟨w, hw, k, hk⟩
    exact hg' w hw k hk
  refine ⟨?_, fun hl => hvl (hvn l hl)⟩
  rintro (h | ⟨-, w, hw, hu⟩)
  · exact hgPl h
  apply hu
  refine HChar.UnrAt.mul ((cf.isMu0 j).unr w fun k hk => hg' w hw k hk) (HChar.UnrAt.mul ?_ ?_)
  · split_ifs with hlp
    · exact cf.isDel'.unr w fun hp => hvS ⟨Or.inr (Or.inr (by rw [if_pos hlp]; exact hoff w hw _ hp)), hvl⟩
    · exact cf.isDel.unr w fun hp => hvS ⟨Or.inr (Or.inr (by rw [if_neg hlp]; exact hoff w hw _ hp)), hvl⟩
  · rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw with e | e
    · rw [← e, eq_plMap_of_conj D hc]
      exact (GlobalTheory.CMVal.InvConj.unrAt_inv_iff ψ hT v).1 (HChar.UnrAt.inv (hψ v hvQ))
    · rw [eq_of_conj D e hc]
      exact hψ v hvQ

end GlobalTheory.MtIn.GenOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupIdentificationFixedPlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteGroupIdentification_fixedPlaces : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → GrpAt X I → LevOf X I U L → ∃ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), IsPlacewiseIdentity X (px := px) eG ∧ (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧ (∀ kv, L.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv) := by
  first | exact @GlobalTheory.Mem.R3.exists_grpIdent | exact GlobalTheory.Mem.R3.exists_grpIdent | (intros; apply GlobalTheory.Mem.R3.exists_grpIdent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostDatumOfPlaceData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Published GlobalTheory.Mem.HD
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.HostDatumExists

theorem exists_reps (K : Type) [Field K] [NumberField K] {ι : Type} [Finite ι] (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (c : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = c ∧
      (∀ i, IsCoprime (I : Ideal (𝓞 K)) (Ideal.span {((n i : ℕ) : 𝓞 K)})) ∧
      ∀ 𝔭 ∈ S, ¬ (I : Ideal (𝓞 K)) ≤ 𝔭.asIdeal := by
  classical
  have := Fintype.ofFinite ι
  set m : Ideal (𝓞 K) := (∏ i, Ideal.span {((n i : ℕ) : 𝓞 K)}) * ∏ 𝔭 ∈ hS.toFinset, 𝔭.asIdeal with hm
  have hm0 : m ≠ ⊥ := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) (Finset.prod_ne_zero_iff.mpr fun 𝔭 _ => 𝔭.ne_bot)
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn i
  obtain ⟨I, hI, hsup⟩ := GlobalTheory.exists_integral_ideal_in_class_coprime K m hm0 c
  refine ⟨I, hI, fun i => ?_, fun 𝔭 h𝔭 hle => 𝔭.isPrime.ne_top ?_⟩
  · rw [Ideal.isCoprime_iff_sup_eq, ← top_le_iff, ← hsup]
    refine sup_le_sup_left (Ideal.le_of_dvd (Dvd.dvd.mul_right ?_ _)) _
    exact Finset.dvd_prod_of_mem (fun i => Ideal.span {((n i : ℕ) : 𝓞 K)}) (Finset.mem_univ i)
  · have h : m ≤ 𝔭.asIdeal :=
      Ideal.le_of_dvd (Dvd.dvd.mul_left
        (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal) (hS.mem_toFinset.mpr h𝔭)) _)
    exact top_le_iff.mp (hsup ▸ sup_le hle h)

theorem le_of_integral {A B : Formalism.L2.Host.Fld} (h : ∀ x ∈ A, IsIntegral ℤ x → x ∈ B) : A ≤ B := by
  intro x hx
  have : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  have h1 : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Qb).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨a, ha, hi⟩ := h1.exists_integral_multiple
  have h2 : a • x ∈ B := h _ (zsmul_mem hx a) hi
  have h3 : x = ((a : Qb))⁻¹ * (a • x) := by
    have : (a : Qb) ≠ 0 := by exact_mod_cast ha
    rw [zsmul_eq_mul, inv_mul_cancel_left₀ this]
  rw [h3]
  exact mul_mem (inv_mem (intCast_mem B a)) h2

end GlobalTheory.HostDatumExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedIntegralOfSeparatingElementStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertiaFixed_integral_of_separating_element : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (σ : G E Ω), σ ∈ Ine (F := E) A' → ∀ (e₀ c : Ω), IsIntegral ℤ e₀ → A.valuation e₀ < A.valuation c → A'.valuation (1 - e₀) < 1 → ∃ e : Ω, IsIntegral ℤ e ∧ σ e = e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  first | exact @GlobalTheory.exists_fixed_of_separating | exact GlobalTheory.exists_fixed_of_separating | (intros; apply GlobalTheory.exists_fixed_of_separating <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerDeepAtOnePlaceUnitAtOther
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TwoPlaces

theorem exists_deep_one_sub :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω)
      (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → A ≠ A' →
      ∀ c : Ω, IsIntegral ℤ c → c ≠ 0 →
        ∃ e : Ω, IsIntegral ℤ e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  intro E Ω _ _ _ _ _ A A' P hA hA' hne c hc hc0
  have hQ : (primeBelow (F := E) A).under (𝓞 E) = P.asIdeal := under_primeBelow hA
  have hQ' : (primeBelow (F := E) A').under (𝓞 E) = P.asIdeal := under_primeBelow hA'
  haveI : (primeBelow (F := E) A).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 E) _
      (by change (Ideal.under (𝓞 E) (primeBelow (F := E) A)).IsMaximal; rw [hQ]; exact P.isMaximal)
  haveI : (primeBelow (F := E) A').IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 E) _
      (by change (Ideal.under (𝓞 E) (primeBelow (F := E) A')).IsMaximal; rw [hQ']; exact P.isMaximal)
  have hQne : primeBelow (F := E) A ≠ primeBelow (F := E) A' := by
    intro h
    apply hne
    refine eq_of_valuation_lt_one_iff E fun b hb => ?_
    have hb' : IsIntegral (𝓞 E) b := hb.tower_top
    have := congrArg (fun I : Ideal (IntCl E Ω) => (⟨b, hb'⟩ : IntCl E Ω) ∈ I) h
    simpa [mem_primeBelow] using this
  have hnle : ¬ primeBelow (F := E) A ≤ primeBelow (F := E) A' := fun h =>
    hQne (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance) h)
  obtain ⟨x, hxQ, hxQ'⟩ := SetLike.not_le_iff_exists.mp hnle
  rw [mem_primeBelow] at hxQ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_pow_valuation_lt_of_integral_algClosure_place E Ω A P hA (x : Ω) c (isIntegral_int_of_isIntegral x.2) hc hc0 hxQ
  have hxk : x ^ k ∉ primeBelow (F := E) A' := fun h => hxQ' (Ideal.IsPrime.mem_of_pow_mem inferInstance k h)
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv inferInstance hxk
  refine ⟨((y * x ^ k : IntCl E Ω) : Ω), isIntegral_int_of_isIntegral (y * x ^ k).2, ?_, ?_⟩
  · rw [MulMemClass.coe_mul, Valuation.map_mul, SubmonoidClass.coe_pow, Valuation.map_pow]
    calc A.valuation (y : Ω) * A.valuation (x : Ω) ^ k ≤ 1 * A.valuation (x : Ω) ^ k :=
          mul_le_mul_left (valuation_le_one_intCl A y) _
      _ < A.valuation c := by rw [one_mul]; exact hk
  · have e1 : (1 : Ω) - ((y * x ^ k : IntCl E Ω) : Ω) = (i : Ω) := by
      have := congrArg (fun z : IntCl E Ω => (z : Ω)) hyi
      simp only [AddMemClass.coe_add, OneMemClass.coe_one] at this
      rw [← this]; ring
    rw [e1]
    exact hi

end GlobalTheory.TwoPlaces
end

