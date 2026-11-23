module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0704
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0637
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentationUnitaryAverage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0696
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0702
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0705
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralShiftHerm
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}
theorem integral_mul_right (m : ℕ) (μ : Measure (Mx D m n)) (hμ : μ.IsAddHaarMeasure) (a : GL (Fin n) (AE D))
    (f : Mx D m n → ℂ) :
    ∫ y, f (HMul.hMul y a.1 : Mx D m n) ∂μ = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(m : ℂ)) * ∫ y, f y ∂μ := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D m n
  haveI : IsTopologicalAddGroup (Mx D m n) := i1
  haveI : LocallyCompactSpace (Mx D m n) := i2
  haveI : SecondCountableTopology (Mx D m n) := i3
  haveI : T2Space (Mx D m n) := i4
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE (1 : GL (Fin m) (AE D)) a
  have hc : addEquivAddHaarChar φ = absA D (Matrix.GeneralLinearGroup.det a) ^ m := by
    have := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) m n
      (1 : GL (Fin m) (AE D)) a
    simpa using this
  have hA : 0 < absA D (Matrix.GeneralLinearGroup.det a) := absA_pos _
  have e : ∀ y : Mx D m n, (HMul.hMul y a.1 : Mx D m n) = φ y := fun y => by
    simp only [φ]
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
  have key : ∫ y, f (φ y) ∂μ = ((((addEquivAddHaarChar φ)⁻¹ : ℝ≥0) : ℝ) : ℂ) * ∫ y, f y ∂μ :=
    integral_comp_char μ φ f
  rw [hc, npow_neg_nat hA] at key
  simp only [e]
  exact key

theorem integral_shift {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (f : A → ℂ) (g : A) :
    ∫ x, f (x - g) ∂μ = ∫ x, f x ∂μ :=
  integral_sub_right_eq_self f g

theorem integral_shift_herm (lam : Measure (hermA D n)) (hl : lam.IsAddHaarMeasure) (f : hermA D n → ℂ) (g : hermA D n) :
    ∫ x, f (x - g) ∂lam = ∫ x, f x ∂lam := by
  obtain ⟨i1, -, -, -, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  exact integral_shift lam f g

theorem halfTr_add (x y : AE D) : halfTr (x + y) = halfTr x + halfTr y := by
  simp [halfTr, mul_add]

theorem halfTr_neg (x : AE D) : halfTr (-x) = -halfTr x := by
  simp [halfTr]

theorem inner_mul_right (V : HSp D) {r : ℕ} (x : Mx D V.rank r) (s : Mx D r r) :
    StdUnn.inner V (HMul.hMul x s : Mx D V.rank r) (HMul.hMul x s : Mx D V.rank r) =
      adj s * StdUnn.inner V x x * s := by
  unfold StdUnn.inner
  rw [adj_mul]
  simp only [Matrix.mul_assoc]

theorem trace_cg (a : GL (Fin n) (AE D)) (c Q : Mx D n n) :
    Matrix.trace (a.1 * c * adj a.1 * (adj (a⁻¹).1 * Q * (a⁻¹).1)) = Matrix.trace (c * Q) := by
  have h1 : a.1 * c * adj a.1 * (adj (a⁻¹).1 * Q * (a⁻¹).1) = a.1 * (c * Q * (a⁻¹).1) := by
    calc _ = a.1 * c * (adj a.1 * adj (a⁻¹).1) * Q * (a⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [adj_mul_adj_inv]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [h1, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

theorem trace_beta (a : GL (Fin n) (AE D)) (B c : Mx D n n) :
    Matrix.trace (B * (a.1 * c * adj a.1)) = Matrix.trace (adj a.1 * B * a.1 * c) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem weil_pt {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (a : GL (Fin n) (AE D)) {m u : G D n} (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) {b1 : Mx D n n}
    (hu : mat u = blk4 1 b1 0 1) (φ : schwartzA θ V.rank n) (y : Mx D V.rank n) :
    (ω (m * u) φ).1 y = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
      (ψ (halfTr (Matrix.trace (b1 * StdUnn.inner V (HMul.hMul y a.1 : Mx D V.rank n) (HMul.hMul y a.1 : Mx D V.rank n)))) *
        φ.1 (HMul.hMul y a.1 : Mx D V.rank n)) := by
  rw [map_mul, Module.End.mul_apply, hω.levi m a hm, hω.unip u b1 hu]

theorem jt_step {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (hμ : μ.IsAddHaarMeasure) (a : GL (Fin n) (AE D)) {m u : G D n} (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1))
    {b1 : hermA D n} (hu : mat u = blk4 1 b1.1 0 1) (φ : schwartzA θ V.rank n) (c : hermA D n) :
    Jt ψ V μ (ω (m * u) φ).1 (cg a c) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
      (npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(V.rank : ℂ)) * Jt ψ V μ φ.1 (c + b1)) := by
  set F : Mx D V.rank n → ℂ := fun y => φ.1 y * ψ (halfTr (Matrix.trace (HMul.hMul (c + b1).1 (StdUnn.inner V y y) : Mx D n n))) with hF
  have hpt : ∀ y : Mx D V.rank n, (ω (m * u) φ).1 y *
      ψ (halfTr (Matrix.trace (HMul.hMul (cg a c).1 (StdUnn.inner V y y) : Mx D n n))) =
      ((χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2)) *
        F (HMul.hMul y a.1 : Mx D V.rank n) := by
    intro y
    have hy : y = (HMul.hMul (HMul.hMul y a.1 : Mx D V.rank n) (a⁻¹).1 : Mx D V.rank n) := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    set Y : Mx D V.rank n := HMul.hMul y a.1 with hY
    have e1 : Matrix.trace (HMul.hMul (cg a c).1 (StdUnn.inner V y y) : Mx D n n) =
        Matrix.trace (c.1 * StdUnn.inner V Y Y) := by
      rw [hy, inner_mul_right]
      exact trace_cg a c.1 _
    rw [weil_pt hω a hm hu, e1]
    simp only [hF]
    have e2 : Matrix.trace (HMul.hMul (c + b1).1 (StdUnn.inner V Y Y) : Mx D n n) =
        Matrix.trace (c.1 * StdUnn.inner V Y Y) + Matrix.trace (b1.1 * StdUnn.inner V Y Y) := by
      rw [← Matrix.trace_add, ← Matrix.add_mul]
      rfl
    rw [e2, halfTr_add, AddChar.map_add_eq_mul]
    ring
  unfold Jt
  simp only [hpt]
  rw [integral_const_mul, integral_mul_right V.rank μ hμ a F]

end GlobalTheory.CompanionTheory.IwaAd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalOfNonIsomorphic
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDisc.Orth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def fixS (V : Submodule ℂ (Sm E N)) (L : Subgroup (GL (Fin N) (Af E))) : Submodule ℂ (Sm E N) where
  carrier := {x | x ∈ V ∧ ∀ u ∈ L, finRep E N u x = x}
  add_mem' := fun {x y} hx hy => ⟨V.add_mem hx.1 hy.1, fun u hu => by rw [map_add (f := _), hx.2 u hu, hy.2 u hu]⟩
  zero_mem' := ⟨V.zero_mem, fun u _ => map_zero _⟩
  smul_mem' := fun c x hx => ⟨V.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩

theorem mem_l2_of_discrete (μ : Measure (GA E N)) [μ.IsHaarMeasure] {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {x : Sm E N}
    (hx : x ∈ V) : x ∈ squareIntegrableSmoothSubmoduleGL μ := mem_l2Sub_of_isAutForm μ (hV.aut x hx) (hV.sqInt x hx)

theorem cont_of_mem {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {x : Sm E N} (hx : x ∈ V) : Continuous x.1 :=
  ContAut.continuous_of_isOpen_stab E N x (hV.aut x hx).level

theorem eq_zero_of_l2Map_eq_zero_of_isDiscrete (μ : Measure (GA E N)) [μ.IsHaarMeasure] {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {x : Sm E N}
    (hx : x ∈ V) (h0 : l2Map μ x = 0) : x = 0 := by
  by_contra hne
  have := re_l2Form_pos μ (mem_l2_of_discrete μ hV hx) (cont_of_mem hV hx) hne
  simp [l2Form, h0] at this

def stabS (x : Sm E N) : Subgroup (GL (Fin N) (Af E)) where
  carrier := {k | finRep E N k x = x}
  mul_mem' := fun {a b} ha hb => by
    change finRep E N (a * b) x = x
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by
    change finRep E N 1 x = x
    rw [map_one, Module.End.one_apply]
  inv_mem' := fun {a} ha => by
    change finRep E N a⁻¹ x = x
    have h : finRep E N a⁻¹ (finRep E N a x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha] at h

theorem exists_repr (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {V V' : Submodule ℂ (Sm E N)}
    (hV : IsDiscrete V) (hV' : IsDiscrete V') {x : Sm E N} (hx : x ∈ V) :
    ∃ y ∈ V', ∀ z ∈ V', ⟪l2Map μ z, l2Map μ x⟫_ℂ = ⟪l2Map μ z, l2Map μ y⟫_ℂ := by
  obtain ⟨L, hLS, hLo, hLc⟩ := GlobalTheory.T.exists_open_compact_subgroup_le E N (stabS x) (hV.aut x hx).level
  have hunit : ∀ (k : Kinf E N) {W W' : Submodule ℂ (Sm E N)}, IsDiscrete W → IsDiscrete W' → ∀ a ∈ W, ∀ b ∈ W',
      ⟪l2Map μ (cptRep E N k a), l2Map μ (cptRep E N k b)⟫_ℂ = ⟪l2Map μ a, l2Map μ b⟫_ℂ :=
    fun k _ _ h h' a ha b hb => (GlobalTheory.T.right_translate_isometry E N μ _ a b (mem_l2_of_discrete μ h ha) (mem_l2_of_discrete μ h' hb)).2
  letI : MeasurableSpace (Kinf E N) := borel _
  haveI : BorelSpace (Kinf E N) := ⟨rfl⟩
  haveI : CompactSpace (Kinf E N) := GlobalTheory.KinfCompactness.compactSpace_Kinf E N
  have key := _root_.GlobalTheory.CompanionTheory.FinDiscRepr.representing_vector (Measure.haar : Measure (Kinf E N)) (cptRep E N) (l2Map μ) (fixS V L) (fixS V' L)
    (fun g : GA E N => (LinearMap.proj g).comp (Sm E N).subtype)
    (fun k a ha b hb => hunit k hV' hV a ha.1 b hb.1)
    (fun k a ha b hb => hunit k hV' hV' a ha.1 b hb.1)
    (fun a ha => by
      obtain ⟨A, h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace E N V hV L a ha.1 ha.2
      exact ⟨A, h1, h2, fun b hb => h3 b hb, h4, h5⟩)
    (fun a ha => by
      obtain ⟨A, h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace E N V' hV' L a ha.1 ha.2
      exact ⟨A, h1, h2, fun b hb => h3 b hb, h4, h5⟩)
    (fun W hW => by
      haveI := GlobalTheory.CompanionTheory.AdmDiscFin.admissible_discrete_spaces E N L W hLo hW V' hV'
      refine Submodule.finiteDimensional_of_le (Submodule.span_mono (t := {φ | φ ∈ V' ∧ TypeB L W φ}) ?_)
      rintro a ⟨ha, hW'⟩
      exact ⟨ha.1, fun u hu g => congrFun (congrArg Subtype.val (ha.2 u hu)) g, hW'⟩)
  have hfx : ∀ u ∈ L, finRep E N u x = x := fun u hu => hLS hu
  obtain ⟨y, hy, hyz⟩ := key x ⟨hx, hfx⟩
  refine ⟨y, hy.1, fun z hz => ?_⟩
  obtain ⟨z', hz', hfix, e⟩ := _root_.GlobalTheory.CompanionTheory.FinDiscAvg.exists_avg E N μ V' hV' L hLc z hz
  rw [e x (mem_l2_of_discrete μ hV hx) hfx, e y (mem_l2_of_discrete μ hV' hy.1) hy.2]
  exact hyz z' ⟨hz', hfix⟩

theorem exists_adj (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (o : Op E N) :
    ∃ o' : Op E N, ∀ {V W : Submodule ℂ (Sm E N)}, IsDiscrete V → IsDiscrete W → ∀ x ∈ V, ∀ y ∈ W,
      ⟪l2Map μ x, l2Map μ (act o y)⟫_ℂ = ⟪l2Map μ (act o' x), l2Map μ y⟫_ℂ := by
  cases o with
  | fin k =>
    refine ⟨.fin k⁻¹, fun {V W} hV hW x hx y hy => ?_⟩
    have h := (GlobalTheory.T.right_translate_isometry E N μ (finGL E N k) (act (.fin k⁻¹) x) y (mem_l2_of_discrete μ hV (hV.stable _ x hx)) (mem_l2_of_discrete μ hW hy)).2
    rw [← h]
    congr 2
    change x = finRep E N k (finRep E N k⁻¹ x)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  | cpt k =>
    refine ⟨.cpt k⁻¹, fun {V W} hV hW x hx y hy => ?_⟩
    have h := (GlobalTheory.T.right_translate_isometry E N μ (infGL E N (Unitary.toUnits k)) (act (.cpt k⁻¹) x) y (mem_l2_of_discrete μ hV (hV.stable _ x hx)) (mem_l2_of_discrete μ hW hy)).2
    rw [← h]
    congr 2
    change x = cptRep E N k (cptRep E N k⁻¹ x)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  | lie X =>
    refine ⟨.lie (-X), fun {V W} hV hW x hx y hy => ?_⟩
    have hxX := hV.stable (.lie X) x hx
    have hyX := hW.stable (.lie X) y hy
    have h := _root_.GlobalTheory.CompanionTheory.FinDiscOrth.lie_skew_l2Map E N μ X x y (cont_of_mem hV hx) (cont_of_mem hW hy) (cont_of_mem hV hxX) (cont_of_mem hW hyX)
      (mem_l2_of_discrete μ hV hx) (mem_l2_of_discrete μ hW hy) (mem_l2_of_discrete μ hV hxX) (mem_l2_of_discrete μ hW hyX)
    have e : act (.lie (-X)) x = - lie E N X x := by
      change lie E N (-X) x = _
      rw [map_neg]; rfl
    rw [e, map_neg, inner_neg_left]
    exact h

theorem isoV_of_ne (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {V V' : Submodule ℂ (Sm E N)}
    (hV : IsDiscrete V) (hV' : IsDiscrete V') {x₀ y₀ : Sm E N} (hx₀ : x₀ ∈ V) (hy₀ : y₀ ∈ V')
    (hne : ⟪l2Map μ y₀, l2Map μ x₀⟫_ℂ ≠ 0) : IsoV V V' := by
  have uniq : ∀ a ∈ V', ∀ b ∈ V', (∀ z ∈ V', ⟪l2Map μ z, l2Map μ a⟫_ℂ = ⟪l2Map μ z, l2Map μ b⟫_ℂ) → a = b := by
    intro a ha b hb h
    have h1 := h (a - b) (V'.sub_mem ha hb)
    rw [← sub_eq_zero, ← inner_sub_right, ← map_sub, inner_self_eq_zero] at h1
    exact sub_eq_zero.1 (eq_zero_of_l2Map_eq_zero_of_isDiscrete μ hV' (V'.sub_mem ha hb) h1)
  choose T hTm hT using fun x : V => exists_repr μ hV hV' x.2
  let Tl : V →ₗ[ℂ] V' :=
    { toFun := fun x => ⟨T x, hTm x⟩
      map_add' := fun x y => Subtype.ext (uniq _ (hTm _) _ (V'.add_mem (hTm x) (hTm y)) fun z hz => by
        rw [← hT _ z hz]
        simp only [Submodule.coe_add, map_add (f := _), inner_add_right]
        rw [← hT x z hz, ← hT y z hz])
      map_smul' := fun c x => Subtype.ext (uniq _ (hTm _) _ (V'.smul_mem c (hTm x)) fun z hz => by
        rw [← hT _ z hz]
        simp only [Submodule.coe_smul, map_smul, inner_smul_right, RingHom.id_apply]
        rw [← hT x z hz]) }
  have hTl : ∀ x : V, (Tl x).1 = T x := fun _ => rfl
  have eqv : ∀ (o : Op E N) (x y : V), y.1 = act o x.1 → (Tl y).1 = act o (Tl x).1 := by
    intro o x y hxy
    obtain ⟨o', ho'⟩ := exists_adj μ o
    refine uniq _ (hTm y) _ (hV'.stable o _ (hTm x)) fun z hz => ?_
    rw [hTl, ← hT y z hz, hxy, ho' hV' hV z hz _ x.2, ho' hV' hV' z hz _ (hTm x),
      hT x _ (hV'.stable o' z hz)]
  have hnz : Tl ≠ 0 := by
    intro h0
    apply hne
    have h1 : T ⟨x₀, hx₀⟩ = 0 := congrArg Subtype.val (LinearMap.congr_fun h0 ⟨x₀, hx₀⟩)
    rw [hT ⟨x₀, hx₀⟩ y₀ hy₀, h1, map_zero, inner_zero_right]
  have hker : LinearMap.ker Tl = ⊥ := by
    have hst : _root_.GlobalTheory.CuspRep.IsStable ((LinearMap.ker Tl).map V.subtype) := by
      rintro o _ ⟨x, hx, rfl⟩
      refine ⟨⟨_, hV.stable o _ x.2⟩, ?_, rfl⟩
      refine Subtype.ext ?_
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hx
      rw [eqv o x _ rfl, hx]
      simp
    rcases hV.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · exact Submodule.map_injective_of_injective V.injective_subtype (by rwa [Submodule.map_bot])
    · exfalso
      refine hnz (LinearMap.ext fun x => ?_)
      have : x.1 ∈ (LinearMap.ker Tl).map V.subtype := by rw [h]; exact x.2
      obtain ⟨x', hx', e⟩ := this
      obtain rfl : x' = x := Subtype.ext e
      exact hx'
  have hran : LinearMap.range Tl = ⊤ := by
    have hst : _root_.GlobalTheory.CuspRep.IsStable ((LinearMap.range Tl).map V'.subtype) := by
      rintro o _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨Tl ⟨_, hV.stable o _ x.2⟩, ⟨_, rfl⟩, eqv o x _ rfl⟩
    rcases hV'.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · exfalso
      have h1 : LinearMap.range Tl = ⊥ :=
        Submodule.map_injective_of_injective V'.injective_subtype (by rwa [Submodule.map_bot])
      exact hnz (LinearMap.range_eq_bot.1 h1)
    · rw [eq_top_iff]
      intro y _
      have : y.1 ∈ (LinearMap.range Tl).map V'.subtype := by rw [h]; exact y.2
      obtain ⟨y', hy', e⟩ := this
      obtain rfl : y' = y := Subtype.ext e
      exact hy'
  refine ⟨LinearEquiv.ofBijective Tl ⟨LinearMap.ker_eq_bot.1 hker, LinearMap.range_eq_top.1 hran⟩, ?_⟩
  intro o x y hxy
  exact eqv o x y hxy

end GlobalTheory.CompanionTheory.FinDisc.Orth


open GlobalTheory.CompanionTheory.FinDisc.Orth in
theorem GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
  ∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → ¬ IsoV V V' →
    ∀ φ ∈ V, ∀ ψ ∈ V', ∫ x in F, φ.1 x * (starRingEnd ℂ) (ψ.1 x) ∂μ = 0 := by
  intro E _ _ _ N mG bG μ _ F hF V V' hV hV' hno φ hφ ψ hψ
  obtain rfl : mG = borel _ := bG.measurable_eq
  haveI := _root_.GlobalTheory.CompanionTheory.AdelicUnimod.isMulRightInvariant_GA_CM E N μ
  rw [_root_.GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner E N μ F hF φ ψ (mem_l2_of_discrete μ hV hφ) (mem_l2_of_discrete μ hV' hψ)]
  by_contra hne
  exact hno (isoV_of_ne μ hV hV' hφ hψ hne)

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSpaceCarriesFlatStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_space_carries_flat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (e₁ : GA E a → ℂ) (e₂ : GA E b → ℂ) (U₁ U₁' : Submodule ℂ (Sm E a)) (U₂ U₂' : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (F : H E a b → ℂ), FlatFn e₁ → FlatFn e₂ → Carries e₁ U₁ U₁' → Carries e₂ U₂ U₂' → F ∈ pairSpace U₁ U₂ → TypeH K₁ K₂ W₁ W₂ F → (fun x => e₁ x.1 * e₂ x.2 * F x) ∈ (pairSpace U₁' U₂' ⊓ typeHF (K₁ ⊓ KO E a) (K₂ ⊓ KO E b) W₁ W₂ : Submodule ℂ (H E a b → ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.pair_carry | exact GlobalTheory.CompanionTheory.LimV.pair_carry | (intros; apply GlobalTheory.CompanionTheory.LimV.pair_carry <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChange
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.SmIntHaar

open MeasureTheory

variable {k : Type} [Field k]

def glLinearEquiv {t : ℕ} (w : GL (Fin t) k) : (Fin t → k) ≃ₗ[k] (Fin t → k) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (w : Matrix (Fin t) (Fin t) k))
    (Matrix.toLin' ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k))
    (by
      rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by
      rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

theorem coe_glLinearEquiv_symm {t : ℕ} (w : GL (Fin t) k) :
    ((glLinearEquiv w).symm : (Fin t → k) → (Fin t → k)) =
      ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec := by
  funext v
  rfl

theorem det_glLinearEquiv {t : ℕ} (w : GL (Fin t) k) :
    LinearEquiv.det (glLinearEquiv w) = Matrix.GeneralLinearGroup.det w := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  show LinearMap.det (Matrix.toLin' (w : Matrix (Fin t) (Fin t) k)) = _
  rw [LinearMap.det_toLin']
  rfl

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem map_inv_mulVec (t : ℕ) [m : MeasurableSpace (Fin t → k)] [hb : BorelSpace (Fin t → k)]
    (μ : Measure (Fin t → k)) [μ.IsAddHaarMeasure] (w : GL (Fin t) k) :
    μ.map ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det w)) • μ := by
  borelize k
  have hp : @BorelSpace (Fin t → k) _ MeasurableSpace.pi := Pi.borelSpace
  have e : m = MeasurableSpace.pi := hb.measurable_eq.trans hp.measurable_eq.symm
  subst e
  rw [← coe_glLinearEquiv_symm, ← det_glLinearEquiv]
  exact GlobalTheory.ChangeVarPi.map_symm_eq_smul k (Fin t) μ (glLinearEquiv w)

theorem smInt_comp_inv_mulVec : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] {Z : Type} [AddCommGroup Z] [Module ℂ Z] (w : GL (Fin t) k) (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → smInt μ (fun v => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v)) = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • smInt μ φ := by
  intro k _ _ _ _ t _ _ μ _ Z _ _ w φ hl _
  have hc : Continuous ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec :=
    continuous_const.matrix_mulVec continuous_id
  have hval : ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) =
      (((distribHaarChar k (Matrix.GeneralLinearGroup.det w) : NNReal) : ℝ) : ℂ) := by
    rw [detChar_apply, val_absPow, Complex.cpow_one]
    rfl
  rw [hval]
  unfold smInt
  rw [smul_finsum]
  refine finsum_congr fun v => ?_
  have hlev : μ ((fun x => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec x)) ⁻¹' {v}) =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det w)) • μ (φ ⁻¹' {v}) := by
    rw [← Measure.smul_apply, ← map_inv_mulVec t μ w]
    exact (Measure.map_apply hc.measurable (hl.isOpen_fiber v).measurableSet).symm
  rw [hlev, ENNReal.toReal_smul, smul_smul, NNReal.smul_def, smul_eq_mul, Complex.ofReal_mul]

end GlobalTheory.CompanionTheory.Rodier.SmIntHaar

end
end

