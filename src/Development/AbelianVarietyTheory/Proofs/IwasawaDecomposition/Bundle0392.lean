module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionProperties
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtRed

section Split

open ReciprocityTheory.Aut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (s : SplitPlace E)

theorem i_mem (a : 𝓞 E) : s.i (a : E) ∈ s.v.adicCompletionIntegers (maximalRealSubfield E) :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (s.split_le_one a)

def iInt : 𝓞 E →+* s.v.adicCompletionIntegers (maximalRealSubfield E) :=
  ((s.i : E →+* s.v.adicCompletion (maximalRealSubfield E)).comp (algebraMap (𝓞 E) E)).codRestrict _ (i_mem s)

theorem mem_max_iff (x : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
    x ∈ IsLocalRing.maximalIdeal (s.v.adicCompletionIntegers (maximalRealSubfield E)) ↔
      Valued.v (x : s.v.adicCompletion (maximalRealSubfield E)) < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

def psiR : 𝓞 E →+* IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield E)) :=
  (IsLocalRing.residue _).comp (iInt s)

theorem psiR_eq_zero (a : 𝓞 E) : psiR s a = 0 ↔ a ∈ s.w.asIdeal := by
  rw [psiR, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
  exact Iff.rfl

theorem psiR_surj : Function.Surjective (psiR s) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hx : Valued.v (x : s.v.adicCompletion (maximalRealSubfield E)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2
  obtain ⟨a, ha⟩ := adic_exists_approx s.v _ hx
  refine ⟨algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a, ?_⟩
  rw [psiR, RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
  have e : ((iInt s (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
      s.v.adicCompletion (maximalRealSubfield E)) = algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) a := by
    show s.i (((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a : 𝓞 E)) : E) = _
    rw [split_coe_algebraMap, AlgHom.commutes]; rfl
  rw [AddSubgroupClass.coe_sub, e, Valuation.map_sub_swap]
  exact ha

def kEqv : kP s.w ≃+* IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield E)) :=
  RingEquiv.ofBijective (Ideal.Quotient.lift s.w.asIdeal (psiR s) fun a ha => (psiR_eq_zero s a).2 ha)
    ⟨by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [Ideal.Quotient.lift_mk, psiR_eq_zero] at hq
      exact Ideal.Quotient.eq_zero_iff_mem.2 hq,
    fun y => by
      obtain ⟨a, rfl⟩ := psiR_surj s y
      exact ⟨Ideal.Quotient.mk s.w.asIdeal a, Ideal.Quotient.lift_mk _ _ _⟩⟩

def phiR : s.v.adicCompletionIntegers (maximalRealSubfield E) →+* kP s.w :=
  ((kEqv s).symm : _ →+* kP s.w).comp (IsLocalRing.residue _)

theorem phiR_surj : Function.Surjective (phiR s) :=
  (kEqv s).symm.surjective.comp IsLocalRing.residue_surjective

theorem phiR_eq_zero (x : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
    phiR s x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield E)) < 1 := by
  rw [phiR, RingHom.comp_apply, RingEquiv.coe_toRingHom, map_eq_zero_iff _ (kEqv s).symm.injective,
    IsLocalRing.residue_eq_zero_iff, mem_max_iff]

theorem kEqv_mk (a : 𝓞 E) : kEqv s (Ideal.Quotient.mk s.w.asIdeal a) = psiR s a :=
  Ideal.Quotient.lift_mk s.w.asIdeal (psiR s) (fun a ha => (psiR_eq_zero s a).2 ha)

theorem phiR_i (a : 𝓞 E) : phiR s ⟨_, i_mem s a⟩ = Ideal.Quotient.mk s.w.asIdeal a := by
  rw [phiR, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq]
  rw [kEqv_mk]; rfl

theorem exists_approx (x : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
    ∃ a : 𝓞 E, Valued.v ((x : s.v.adicCompletion (maximalRealSubfield E)) - s.i (a : E)) < 1 ∧
      phiR s x = Ideal.Quotient.mk s.w.asIdeal a := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := s.w.asIdeal) (phiR s x)
  refine ⟨a, ?_, ha.symm⟩
  have h : phiR s (x - ⟨_, i_mem s a⟩) = 0 := by
    rw [map_sub, phiR_i, ha, sub_self]
  have h2 := (phiR_eq_zero s _).1 h
  rwa [AddSubgroupClass.coe_sub] at h2

end Split

end GlobalTheory.MtRed

end

noncomputable section

namespace GlobalTheory.MtRed

variable (D : D7) (n : ℕ)

theorem km_mem_UA (κ : Formalism.AUTREP.GAf D.host.E n) : km D n κ ∈ UA D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) := by
  show Formalism.UG.cT (GlobalTheory.StdFrameExist.sgA D) (GlobalTheory.StdFrameExist.kmat κ).1 *
      (1 : Matrix (Fin n) (Fin n) D.host.E).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *
      (GlobalTheory.StdFrameExist.kmat κ).1 = (1 : Matrix (Fin n) (Fin n) D.host.E).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, GlobalTheory.StdFrameExist.cT_kmat]

theorem km_mem_St_iff (κ : Formalism.AUTREP.GAf D.host.E n) :
    km D n κ ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (EAf D)) ↔ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n := by
  rw [GlobalTheory.StdFrameExist.mem_Umax_iff]
  constructor
  · rintro ⟨y, hy⟩ i j
    have e : (GlobalTheory.StdFrameExist.kmat κ).1 i j = ((y.1 i j : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      show (km D n κ).1 i j = _
      rw [← hy]
      simp [frGL, intGL, Formalism.UG.bc]
    rw [e]
    exact (y.1 i j).2
  · intro h
    have h' : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 :=
      (GlobalTheory.StdFrameExist.mem_Umax_iff _).1 (inv_mem ((GlobalTheory.StdFrameExist.mem_Umax_iff κ).2 h))
    have hm : (GlobalTheory.StdFrameExist.kmat κ).1 * (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 = 1 := by
      rw [GlobalTheory.StdFrameExist.kmat_inv, Units.mul_inv]
    have hm' : (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 * (GlobalTheory.StdFrameExist.kmat κ).1 = 1 := by
      rw [GlobalTheory.StdFrameExist.kmat_inv, Units.inv_mul]
    refine ⟨⟨Matrix.of fun i j => ⟨_, h i j⟩, Matrix.of fun i j => ⟨_, h' i j⟩, ?_, ?_⟩, ?_⟩
    · ext i j
      have := congrFun (congrFun hm i) j
      rw [Matrix.mul_apply] at this
      rw [Matrix.mul_apply]
      push_cast
      show ∑ x, (GlobalTheory.StdFrameExist.kmat κ).1 i x * (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 x j = _
      rw [this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · ext i j
      have := congrFun (congrFun hm' i) j
      rw [Matrix.mul_apply] at this
      rw [Matrix.mul_apply]
      push_cast
      show ∑ x, (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 i x * (GlobalTheory.StdFrameExist.kmat κ).1 x j = _
      rw [this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · apply Units.ext
      ext i j
      simp [frGL, intGL, Formalism.UG.bc]
      rfl

theorem red_eq_one (κ : Formalism.AUTREP.GAf D.host.E n) (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (PP : Pl D.host.E) (hT : ReciprocityTheory.Aut.TrivOutside A κ) (hP : NG.OverPl PP v) (hv : v ∉ A) :
    redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1 := by
  refine Formalism.L2.DIV.reduction_local D.host.F D.host.E n 1 PP v hP.symm _ ((km_mem_St_iff D n κ).2 hκ) ?_
  have h := hT v hv
  apply Units.ext
  ext i j
  have e := congrFun (congrFun h i) j
  rw [Matrix.map_apply] at e
  exact e

end GlobalTheory.MtRed

end

noncomputable section

namespace GlobalTheory.MtRed

variable (D : D7) (n : ℕ)

theorem red_split (κ : Formalism.AUTREP.GAf D.host.E n) (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a b : Fin n) :
    ∃ h : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      (redFn (1 : GL (Fin n) (EAf D)) s.w (km D n κ)).val a b = phiR s ⟨_, h⟩ := by
  obtain ⟨y, hy⟩ := (km_mem_St_iff D n κ).2 hκ
  have hz : (κ.1.val a b) ∈ ReciprocityTheory.Aut.ALint D.host.E := hκ a b
  have hz' := GlobalTheory.RowGood.tr_int rfl hz
  rw [GlobalTheory.RowGood.tr_rfl] at hz'
  have hmem : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (GlobalTheory.RowGood.proj_le_one s hz')
  refine ⟨hmem, ?_⟩
  obtain ⟨c, hc, hφ⟩ := exists_approx s ⟨_, hmem⟩
  rw [hφ]
  have hyab : ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = κ.1.val a b := by
    have e : (km D n κ).1 a b = ((y.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      rw [← hy]
      simp [frGL, intGL, Formalism.UG.bc]
    exact e.symm
  rw [← hy, redFn_frGL]
  have := GlobalTheory.RowGood.res_eq (rfl : maximalRealSubfield D.host.E = _) s (κ.1.val a b) (y.val a b)
    (by rw [GlobalTheory.RowGood.tr_rfl]; exact hyab) c hc
  exact this

end GlobalTheory.MtRed

end

namespace GlobalTheory.MtRed

theorem km_reduction : ∀ (D : D7) (n : ℕ), (∀ κ, km D n κ ∈ UA D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E)) ∧ (∀ κ, km D n κ ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (EAf D)) ↔ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n) ∧ (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v) (PP : Pl D.host.E), ReciprocityTheory.Aut.TrivOutside A κ → NG.OverPl PP v → v ∉ A → redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1) ∧ ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w, Function.Surjective φ ∧ (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) ∧ (∀ a : 𝓞 D.host.E, ∃ h : s.i (a : D.host.E) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), φ ⟨_, h⟩ = Ideal.Quotient.mk _ a) ∧ ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ a b, ∃ h : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), (redFn (1 : GL (Fin n) (EAf D)) s.w (km D n κ)).val a b = φ ⟨_, h⟩ := by
  intro D n
  exact ⟨km_mem_UA D n, km_mem_St_iff D n, fun κ hκ A v PP hT hP hv => red_eq_one D n κ hκ A v PP hT hP hv,
    fun s => ⟨phiR s, phiR_surj s, phiR_eq_zero s, fun a => ⟨i_mem s a, phiR_i s a⟩,
      fun κ hκ a b => red_split D n κ hκ s a b⟩⟩

end GlobalTheory.MtRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepBeforeClNonempty
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.Mem.Col2.TC.stepBefore_cl_nonempty {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (u : B.Word) :
    Nonempty (I.stp u I.mu0 (B.R.m - 1)).Cl := by
  classical
  have hm2 := B.R.two_le_m
  have hmj : B.R.m - 1 + 1 = B.R.m := by omega
  have hL := hOk.idx_ok I.mu0
  obtain ⟨b0x, -⟩ := hL.last_uniq
  let b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) (B.R.m - 1) := ⟨some (cast (by rw [show B.R.m - 1 = B.R.m - 2 + 1 by omega]) b0x), by simp; omega⟩
  let q0 : (I.stp u I.mu0 (B.R.m - 1)).D b0 := ⟨(DecoF.base _ _ _ _ _, {z | z - 0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup I.mu0)) (DecoF.base B.fields.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K))).deco.1.N
      (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst I.mu0).M : ℤ))}), by
    show _ ∈ (ysAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) (B.R.m - 1)).ys _
    rw [ysAt_ys_of_eq _ _ _ hmj]
    exact ⟨0, zero_mem _, rfl⟩⟩
  exact ⟨(I.stp u I.mu0 (B.R.m - 1)).cl b0 q0⟩


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Mem.Col2.TC.levJ_herm_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → 1 ≤ B.R.m - 1 → ∃ H0 : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) (I.rec7 l Z).host.g (B.T u) B.R.f, F.levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) H0.Lb ∧ ∀ v, F.levJ.Uloc v = (H0.Uloc v).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom := by
  intro B X I hI hP l Z u Ch0 chOf0 F hF h1
  have hi : B.R.m - 1 ≤ (I.rec7 l Z).R.m := Nat.sub_le _ _
  have hgram : gramN (I.rec7 l Z) (B.R.m - 1) hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 (B.R.m - 1) hi).1
  haveI : NeZero ((I.rec7 l Z).R.N (B.R.m - 1)) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s F.atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact F.atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  obtain ⟨c0⟩ := GlobalTheory.Mem.Col2.TC.stepBefore_cl_nonempty I hI u
  obtain ⟨k, H⟩ := hF.mid (B.R.m - 1) h1 (succ_pred_m _)
  have hLb : ∀ x, x ∈ F.levJ.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N (B.R.m - 1)) (X.piT u) := by
    intro x
    rw [← F.levJ_Lb h1 (chOf0 (B.R.m - 1) c0)]
    exact H.lb _ x
  have hL : F.levJ.Lb = rll_dLat ((I.rec7 l Z).R.N (B.R.m - 1)) (((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ F.atT.piU hp0 F.levJ.Lb ?_
    rw [hF.piU]; exact hLb
  have hE := GlobalTheory.Mem.Col2.Lv.exists_herm_level (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) (rankN (I.rec7 l Z) (B.R.m - 1) hi)
    (I.rec7 l Z).host.g _ _ rfl F.levJ ?_ ?_ ?_
  · obtain ⟨L, e1, e2, -⟩ := hE
    exact ⟨L, e1, e2⟩
  · intro v h0 h1 hb
    rcases hb with hb | hb
    · exact h0 hb
    · exact h1 hb
  · intro a v h x hx hp
    exact GlobalTheory.Mem.LevCong.mem_Uloc_of_cong _ F.levJ F.gl F.glevJ a v h x hx hp
  · intro v h x
    exact GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram F.levJ F.atT.piU (s F.atT.piU) rfl hpq hTp hL v h (_root_.GlobalTheory.LevelUnif.dvd_of_val_lt_one (I.rec7 l Z) u F.atT v h) x

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesAwayLevelAndTypePrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TwistPrimes

open GlobalTheory.Mem.LevTwist ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

theorem twist_primes_away : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (I.Q I.mu0 = ∅) ∧ ∀ (u : B.Word) (a : I.ι), ∀ P ∈ I.Q a, (P ∉ (B.primes X).vT u ∧ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ (B.primes X).vT u ∧ conjPrime₂ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ I.Q a) ∧ X.piT u ∉ P.asIdeal ∧ (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  intro B X I h
  refine ⟨I.twistPrimes_reference_tuple_eq_empty, fun u a P hP => ?_⟩
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hg := good_of_mem h (I.Q_subset_SQ a hP)
  have hS := hg.2.2.2
  have hu : (conjPrime₂ P).under (𝓞 B.host.F) = P.under (𝓞 B.host.F) := (under_eq_iff B.host P _).2 (Or.inr rfl)
  have hT : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      ((B.primes X).T u : 𝓞 B.host.E) ∉ R.asIdeal := fun R hR hm => hS (by
    rw [← hR, (ReadTwist.plc_under_eq_iff (F := B.host.F) R (hPr.T_prime u)).2 hm]
    exact h.T_mem u)
  have hpi : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      (B.primes X).piT u ∉ R.asIdeal := fun R hR hm => hT R hR (by
    rw [← hPr.piT_norm u]; exact Ideal.mul_mem_right _ _ hm)
  have h0 : (B.primes X).piT u ≠ 0 := fun e => by
    have := hPr.piT_norm u
    rw [e, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have hvT : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      R ∉ (B.primes X).vT u := fun R hR hm => hpi R hR ((mem_divs h0 _).1 hm)
  have hvG : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      R ∉ (B.primes X).vGs := fun R hR hm => hS (by rw [← hR]; exact plc_mem h hm)
  refine ⟨⟨hvT P rfl, hvG P rfl, hvT _ hu, hvG _ hu, fun hc => ?_⟩, hpi P rfl, fun hm => hT P rfl ?_⟩
  · have e := (good_of_mem h (I.Q_subset_SQ a hc)).1
    rw [hu, hg.1] at e
    exact conjP_ne B.host ((GoodPlace.goodPl_under_iff _ B.host _ P).1 hg.2).1 e.symm
  · rw [← map_natCast (algebraMap (𝓞 B.host.F) (𝓞 B.host.E))]
    exact hm

end GlobalTheory.Mem.Col2.TwistPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLeOneIffOfContinuous
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.IsoInteg

open ValuativeRel Filter Topology

section Val

variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem tendsto_pow_zero_of_lt_one {x : K} (h : valuation K x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous (i : K →+* K') (hi : Continuous i) {x : K} (h : valuation K x < 1) :
    valuation K' (i x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => i x ^ n) atTop (𝓝 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_zero_of_lt_one h)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : K' | valuation K' y < 1} ∈ 𝓝 (0 : K') :=
    (IsValuativeTopology.hasBasis_nhds_zero' K').mem_iff.2 ⟨1, one_ne_zero, fun y hy => hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ valuation K' (i x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_one_of_map_le_one (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K' (i y) ≤ 1) :
    valuation K y ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  have h1 : valuation K y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := lt_one_of_continuous i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h0 : (0 : ValueGroupWithZero K') < valuation K' (i y) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact (map_ne_zero i).2 hy
  exact absurd h (not_le.2 ((inv_lt_one₀ h0).1 h2))

theorem map_le_one (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K y ≤ 1) :
    valuation K' (i y) ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
  have hx : x ≠ 0 := fun h0 => hx0 (by simp [h0])
  have hγ : valuation K' (i x) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact (map_ne_zero i).2 hx
  have hpos : (0 : ValueGroupWithZero K') < valuation K' (i y) := zero_lt_one.trans hc
  have hinv : valuation K' (i y)⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have ht := tendsto_pow_zero_of_lt_one hinv
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K').tendsto_right_iff] at ht
  obtain ⟨n, hn⟩ := (ht _ hγ).exists
  have hxy : valuation K (x * y ^ n) < 1 := by
    rw [map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' h n)) hx1
  have h2 := lt_one_of_continuous i hi hxy
  rw [map_mul, map_pow, map_mul, map_pow] at h2
  simp only [Set.mem_setOf_eq, map_pow, map_inv₀] at hn
  have hpn : (0 : ValueGroupWithZero K') < valuation K' (i y) ^ n := pow_pos hpos n
  rw [inv_pow] at hn
  have := (inv_lt_iff_one_lt_mul₀ hpn).1 hn
  exact absurd h2 (not_lt.2 this.le)

end Val

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem valued_le_one_iff_of_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E),
    Continuous i → ∀ a : v.adicCompletion F, Valued.v (i a) ≤ 1 ↔ Valued.v a ≤ 1 := by
  intro F E _ _ _ _ v w i hi a
  rw [← GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff w, ← GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff v]
  exact ⟨le_one_of_map_le_one i.toRingHom hi, map_le_one i.toRingHom hi⟩

end GlobalTheory.IsoInteg

end
end

