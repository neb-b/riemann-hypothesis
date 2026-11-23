module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicFrameTorusElementMatrixEq
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

theorem mat_eq_of_isIdTorusElt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J}, IsIdTorusElt σ J X Y l a →
    (matHom _ σ J a).1 = 1 + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) Y * J)
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) X * J) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW l a ha
  obtain ⟨h1, h2, h3⟩ := ha
  have hxx : adMat F (cT (σ : E →+* E) X * J) * adMat F X = 0 := by
    rw [← Matrix.map_mul, hW.xx, Matrix.map_zero _ (map_zero _)]
  have hxy : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := by
    rw [← Matrix.map_mul, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [← Matrix.map_mul, GlobalTheory.StdPar.yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyy : adMat F (cT (σ : E →+* E) Y * J) * adMat F Y = 0 := by
    rw [← Matrix.map_mul, hW.yy, Matrix.map_zero _ (map_zero _)]
  set A := (matHom _ σ J a).1 with hAdef
  set Xs := adMat F (cT (σ : E →+* E) X * J) with hXs
  set Ys := adMat F (cT (σ : E →+* E) Y * J) with hYs
  set P := 1 - adMat F X * Ys - adMat F Y * Xs with hP
  have hXP : Xs * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hxx, hxy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hYP : Ys * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hyx, hyy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hAP : A * P = P := by
    ext i j
    have hz : (fun k => P k j) ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ := by
      rw [Submodule.mem_inf]
      refine ⟨?_, ?_⟩
      · simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
        intro k _
        change (Xs *ᵥ fun k => P k j) k = 0
        rw [show (Xs *ᵥ fun k => P k j) k = (Xs * P) k j from rfl, hXP]; rfl
      · simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
        intro k _
        change (Ys *ᵥ fun k => P k j) k = 0
        rw [show (Ys *ᵥ fun k => P k j) k = (Ys * P) k j from rfl, hYP]; rfl
    have := congrFun (h3 _ hz) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hsum : P + adMat F X * Ys + adMat F Y * Xs = 1 := by rw [hP]; abel
  have hA : A = P + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) * Ys
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) * Xs := by
    calc A = A * (P + adMat F X * Ys + adMat F Y * Xs) := by rw [hsum, Matrix.mul_one]
      _ = _ := by
        rw [Matrix.mul_add, Matrix.mul_add, hAP, ← Matrix.mul_assoc, h1, ← Matrix.mul_assoc A, h2]
  have hd : ∀ f : Fin r → AF F ⊗[F] E, diagonal (fun k => f k - 1) = diagonal f - 1 := fun f => by
    rw [← diagonal_one, diagonal_sub]
  rw [hA, hd, hd, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one, hP]
  abel

end GlobalTheory.IdTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CurveRootGeometry

section Defs

variable {O : Type} [CommRing O]

def IsActPull {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] (i' : OAct O G') (i : OAct O G)
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) : Prop :=
  IsGrpPullback G' G f φ ∧ ∀ a, (i'.act a).left ≫ φ = φ ≫ (i.act a).left

def IsCover (k : Type) [Field k] {C C' : Scheme.{0}} [Algebra k Γ(C, ⊤)] [Algebra k Γ(C', ⊤)] (π : C' ⟶ C) : Prop :=
  IsFinite π ∧ Surjective π ∧ π ≫ strHom k C = strHom k C'

def IsRosati (c : O →+* O) {S : Scheme.{0}} (P : Out.PolAV S) (j : OAct O P.A) : Prop :=
  ∀ a, Out.RosatiAdj P.A P.L (j.act a) (j.act (c a))

def PolPart (c : O →+* O) {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (T : TorusExtension G) (P : Out.PolAV (Sp K)) (e : T.B ≅ P.A) (j : OAct O P.A),
    IsMonHom (T.q ≫ e.hom) ∧ (∀ a, i.act a ≫ T.q ≫ e.hom = (T.q ≫ e.hom) ≫ j.act a) ∧ IsRosati c P j

def genPt (C : Scheme.{0}) [IsIntegral C] : Sp C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)

def geomGenPt (C : Scheme.{0}) [IsIntegral C] : Sp (AlgebraicClosure C.functionField) ⟶ C :=
  spMap (algebraMap C.functionField (AlgebraicClosure C.functionField)) ≫ genPt C

def PolGen (c : O →+* O) {C : Scheme.{0}} [IsIntegral C] {G : Over C} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (G' : Over (Sp (AlgebraicClosure C.functionField))) (_ : GrpObj G') (i' : OAct O G') (φ : G'.left ⟶ G.left),
    IsActPull i' i (geomGenPt C) φ ∧ PolPart c i'

def AbGen (c : O →+* O) {C : Scheme.{0}} [IsIntegral C] {G : Over C} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (P : Out.PolAV (Sp C.functionField)) (j : OAct O P.A) (φ : P.A.left ⟶ G.left),
    IsActPull j i (genPt C) φ ∧ IsRosati c P j

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

end Defs

def Splits (O k : Type) [CommRing O] [Field k] : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (τ : κ → (O →+* k)), IsSplitBy τ

section Lemmas

variable {O : Type} [CommRing O]

theorem IsActPull.comp {S S' S'' : Scheme.{0}} {G'' : Over S''} [GrpObj G''] {G' : Over S'} [GrpObj G'] {G : Over S}
    [GrpObj G] {i'' : OAct O G''} {i' : OAct O G'} {i : OAct O G} {g : S'' ⟶ S'} {f : S' ⟶ S} {φ' : G''.left ⟶ G'.left}
    {φ : G'.left ⟶ G.left} (h' : IsActPull i'' i' g φ') (h : IsActPull i' i f φ) : IsActPull i'' i (g ≫ f) (φ' ≫ φ) :=
  ⟨h'.1.comp h.1, fun a => by rw [← Category.assoc, h'.2, Category.assoc, h.2, Category.assoc]⟩

end Lemmas

end GlobalTheory.CurveRootGeometry
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarJacobianDetEqZeroOfCompactSupport
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem contDiffOn_dbar_apply {n : ℕ} {U : Set (V n)} {f : V n → ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (ξ : V n) : ContDiffOn ℝ 1 (fun x => dbar f x ξ) U := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y) U := hf.fderiv_of_isOpen hU (by norm_num)
  have ha : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y ξ) U := h1.clm_apply contDiffOn_const
  have hb : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y (Complex.I • ξ)) U :=
    h1.clm_apply contDiffOn_const
  have : (fun x => dbar f x ξ) =
      fun x => (1 / 2 : ℂ) • (fderiv ℝ f x ξ + Complex.I • fderiv ℝ f x (Complex.I • ξ)) := by
    funext x; exact dbar_apply f x ξ
  rw [this]
  exact (ha.add (hb.const_smul Complex.I)).const_smul _

theorem integral_dbarJacobian_eq_zero : ∀ {n : ℕ} (U K : Set (V n)) (f : Fin n → V n → ℂ) (j : Fin n),
    IsOpen U → IsCompact K → K ⊆ U → (∀ i, ContDiffOn ℝ 2 (f i) U) →
    (∀ v ∈ U, v ∉ K → f j v = 0) →
    ∫ v in U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  intro n U K f j hU hK hKU hf hz
  have hgC : ∀ w : Equiv.Perm (Fin n), ContDiffOn ℝ 1
      (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) U := fun w =>
    ((hf j).of_le (by norm_num)).mul
      (contDiffOn_prod fun i _ => contDiffOn_dbar_apply hU (hf i) _)
  have hg0 : ∀ w : Equiv.Perm (Fin n), ∀ v ∈ U, v ∉ K →
      (f j v * ∏ i ∈ Finset.univ.erase j, dbar (f i) v (coordVec (w i))) = 0 :=
    fun w v hv hvK => by rw [hz v hv hvK, zero_mul]
  have hT := fun w : Equiv.Perm (Fin n) =>
    GlobalTheory.T.integral_antiholomorphicDeriv_compactSupport_eq_zero U K _ (coordVec (w j)) hU hK hKU (hgC w) (hg0 w)
  have hcongr : ∫ v in U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det =
      ∫ v in U, ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) *
        dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v
          (coordVec (w j)) :=
    setIntegral_congr_fun hU.measurableSet fun v hv =>
      _root_.GlobalTheory.GoodTop.det_dbar_eq_sum_dbar f j v fun i => (hf i).contDiffAt (hU.mem_nhds hv)
  rw [hcongr, integral_finsetSum _ fun w _ => (hT w).1.const_mul _]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [integral_const_mul, (hT w).2, mul_zero]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberGlobalSectionEqSumCycle
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecCycle

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh

theorem coheight_eq_one_of_dim_closure {X : Scheme.{0}} {n : ℕ}
    (hX : topologicalKrullDim X ≤ (n + 1 : ℕ)) {w : X} (hw : ¬ IsMax w)
    (hd : topologicalKrullDim (closure ({w} : Set X)) = n) : Order.coheight w = 1 := by
  have key : ∀ {a b : X}, a < b → topologicalKrullDim (closure ({a} : Set X)) + 1 ≤
      topologicalKrullDim (closure ({b} : Set X)) := by
    intro a b hab
    refine topologicalKrullDim_add_one_le isClosed_closure isClosed_closure
      fun x hx => ⟨b, subset_closure rfl, fun hb => ?_, ?_⟩
    · exact hab.not_ge (specializes_iff_mem_closure.2 hb)
    · have h1 : b ⤳ a := hab.le
      have h2 : a ⤳ x := specializes_iff_mem_closure.2 hx
      exact h1.trans h2
  have hle : ∀ b : X, topologicalKrullDim (closure ({b} : Set X)) ≤ topologicalKrullDim X :=
    fun b => Topology.IsInducing.subtypeVal.topologicalKrullDim_le
  refine le_antisymm ((Order.coheight_le_coe_iff (n := 1)).2 fun y hy => ?_) ?_
  · by_contra hc
    have hy0 : ¬ IsMax y := fun h => hc (by rw [Order.coheight_eq_zero.2 h]; exact zero_lt_one)
    obtain ⟨b, hyb⟩ := not_isMax_iff.1 hy0
    have h := ((add_le_add (hd ▸ key hy : (n : WithBot ℕ∞) + 1 ≤ _) (le_refl (1 : WithBot ℕ∞))).trans
      (key hyb)).trans ((hle b).trans hX)
    norm_cast at h
    omega
  · rw [ENat.one_le_iff_ne_zero]
    exact fun h => hw (Order.coheight_eq_zero.1 h)

open scoped Pointwise

theorem mult_divOfSec_eq_length_cut {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {M : LB X} (hM : M.IsLB) (s : M.Sec) (hs : genericPoint X ∈ nonzeroLocus s) {w : X}
    (hw : Order.coheight w = 1) :
    (divOfSec hM s hs).mult w = ((Module.length (X.presheaf.stalk w)
      ((cut (structureModule X) hM s).presheaf.stalk w :)).toNat : ℤ) := by
  obtain ⟨i, hi⟩ := exists_chart hM w
  obtain ⟨q⟩ := CutDegree.nonempty_stalk_cut_equiv (structureModule X) hM s i hi
  set g := X.presheaf.germ _ w hi (s.f i)
  have e1 : Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {g}) =
      Module.length (X.presheaf.stalk w) (QuotSMulTop g (X.presheaf.stalk w)) := by
    refine (Submodule.quotEquivOfEq (Ideal.span {g}) (g • (⊤ : Submodule (X.presheaf.stalk w)
      (X.presheaf.stalk w))) ?_).length_eq
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [mult_divOfSec hw hi, ← q.length_eq,
    (QuotSMulTop.congr g (structureModuleStalkEquiv w)).length_eq, ← e1]

theorem mult_divOfSec_ne_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {M : LB X} (hM : M.IsLB) (s : M.Sec) (hs : genericPoint X ∈ nonzeroLocus s) {w : X}
    (hw : Order.coheight w = 1) (hws : w ∉ nonzeroLocus s) : (divOfSec hM s hs).mult w ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_chart hM w
  have : Ring.KrullDimLE 1 (X.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
  have e := algebraMap_germ hi (s.f i)
  have hg0 : X.presheaf.germ _ w hi (s.f i) ≠ 0 := fun h0 => fnOf_sec_ne_zero hs (gen_mem hi)
    (e.symm.trans ((congrArg _ h0).trans (map_zero _)))
  have htop := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hg0)
  have hu : ¬ IsUnit (X.presheaf.germ _ w hi (s.f i)) := fun h =>
    hws ((mem_nonzeroLocus_iff s i hi).2 ((Scheme.mem_basicOpen _ _ _ _).2 h))
  rw [mult_divOfSec hw hi, Nat.cast_ne_zero, Ne, ENat.toNat_eq_zero, not_or]
  refine ⟨fun h0 => hu ?_, htop⟩
  rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top] at h0
  exact h0

theorem interNum_cons_eq_finsum_mult : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (s : M.Sec) (hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfSec hM s hs).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  intro κ _ X _ _ _ hproj n hX M hM P hP s hs
  have hf := algebraMap_eq_strHom κ X
  have := isNoetherian_of_isProjOver hproj
  have : IsProper (strHom κ (X := X)) := (isProper_and_exists_isAmpleLB_of_isProjOver hproj).1
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hproj
  have hmono := (mono_cutHom_structureModule_iff hM s).2 hs
  have hfin : FiniteCohTwists κ (structureModule X) := hH.finiteCohTwists hf _
  rw [interNum_cons_eq_interNum_cut hM s hP hfin]
  have hsupp : suppDim (cut (structureModule X) hM s) ≤ (Fintype.card (Fin n) : ℕ) := by
    rw [Fintype.card_fin]
    exact suppDim_cut_le _ hM s (by rwa [QCoh.suppDim_structureModule])
  have hfs := (divOfSec hM s hs).finite_support_mult
  have hS : ∀ w ∈ support (cut (structureModule X) hM s),
      topologicalKrullDim (closure ({w} : Set X)) = (Fintype.card (Fin n) : ℕ) → w ∈ hfs.toFinset := by
    intro w hw hd
    rw [Fintype.card_fin] at hd
    rw [support_cut, QCoh.support_structureModule] at hw
    have hmax : ¬ IsMax w := fun h => hw.2 ((h (genericPoint_specializes w) :
      w ⤳ genericPoint X).mem_open (nonzeroLocus s).isOpen hs)
    have hc := coheight_eq_one_of_dim_closure hX hmax hd
    simpa using mult_divOfSec_ne_zero hM s hs hc hw.2
  rw [T.intersectionNumber_sheaf_eq_sum_length_mul_cycle κ X hproj (Fin n) P hP _ hsupp hfs.toFinset hS,
    finsum_eq_sum_of_support_subset _ (s := hfs.toFinset) ?_]
  · refine Finset.sum_congr rfl fun w hw => ?_
    have hw' : (divOfSec hM s hs).mult w ≠ 0 := by simpa using hw
    rw [mult_divOfSec_eq_length_cut hM s hs (CartierDiv.coheight_eq_one_of_mult_ne_zero hw')]
  · intro w hw
    simpa using Function.support_mul_subset_left _ _ hw

end GlobalTheory.SecCycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberNonnegOfNefAmpleAddNef
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem interNum_nonneg_of_isNef_of_ample_tens_nef (k : Type) [Field k] [Infinite k]
    (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (hX : IsProjOver (strHom k (X := X)))
    (hAN : ∀ A N : LB X, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N))
    (d : ℕ) (F : X.Modules) [IsFiniteQC F] (hd : suppDim F ≤ (d : ℕ))
    (P : Fin d → LB X) (hP : ∀ i, IsNef k (P i)) : 0 ≤ interNum k F P := by
  classical
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hX
  have hD : DiffVanish (d + 1) (chiPic k F) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) F hX hd
  have key : ∀ S : Finset (Fin d), ∀ Q : Fin d → LB X, (∀ i ∈ S, IsNef k (Q i)) →
      (∀ i ∉ S, IsAmpleLB (Q i)) → 0 ≤ interNum k F Q := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun Q _ h ↦ GlobalTheory.T.lineBundleIntersectionNumber_nonneg_of_ample k X hX d F hd Q fun i ↦ h i (by simp)
    | insert i S hi ih =>
      intro Q hn ha
      have hi' : IsNef k (Q i) := hn i (Finset.mem_insert_self _ _)
      have hL : ∀ j, (Q j).IsLB := fun j ↦ by
        by_cases h : j ∈ insert i S
        · exact (hn j h).isLB
        · exact (ha j h).isLB
      have h1 : ∀ B : LB X, IsAmpleLB B → 0 ≤ interNum k F (Function.update Q i B) := by
        intro B hB
        refine ih _ (fun j hj ↦ ?_) (fun j hj ↦ ?_)
        · rw [Function.update_of_ne (by rintro rfl; exact hi hj)]
          exact hn j (Finset.mem_insert_of_mem hj)
        · by_cases h : j = i
          · subst h; rwa [Function.update_self]
          · rw [Function.update_of_ne h]
            exact ha j (by simp [h, hj])
      have h2 : ∀ m : ℕ, ∃ B : LB X, IsAmpleLB B ∧ interNum k F (Function.update Q i B) =
          interNum k F (Function.update Q i A) + m * interNum k F Q := by
        intro m
        induction m with
        | zero => exact ⟨A, hA, by simp⟩
        | succ m ihm =>
          obtain ⟨B, hB, e⟩ := ihm
          refine ⟨tens B (Q i), hAN _ _ hB hi', ?_⟩
          rw [hD.interNum_update_tens (by simp) hL i hB.isLB (hL i), e, Function.update_eq_self]
          push_cast
          ring
      by_contra hneg
      obtain ⟨B, hB, e⟩ := h2 ((interNum k F (Function.update Q i A)).toNat + 1)
      have h3 := h1 B hB
      have h4 := h1 A hA
      rw [e] at h3
      push_cast at h3
      rw [Int.toNat_of_nonneg h4] at h3
      nlinarith
  exact key Finset.univ P (fun i _ ↦ hP i) (fun i h ↦ absurd (Finset.mem_univ i) h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicMvPolynomialEvalAdjoinEtaleTowerCoordStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraic_mvPolynomialEval_adjoin_etaleTowerCoords : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  (letI := cL.toAlgebra; ∀ a : MvPolynomial (Fin r) R,
    IsAlgebraic (Algebra.adjoin ℂ (Set.range (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))))
      ((MvPolynomial.eval₂Hom ι τ a : T) : L)) := by
  first | exact @GlobalTheory.FieldPair.TowerTrdeg.image_isAlgebraic | exact GlobalTheory.FieldPair.TowerTrdeg.image_isAlgebraic | (intros; apply GlobalTheory.FieldPair.TowerTrdeg.image_isAlgebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefOfNonzeroSectionPowInduction
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem isAmpleLB_tens_of_nef_of_hasNonzeroSec_pow_step : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ A M : LB X, IsAmpleLB A → IsNef k M → (∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r)) → IsAmpleLB (tens A M) := by
  intro k _ _ d hd X _ _ hp hX A M hA hM hsec
  obtain ⟨r, hr, hs⟩ := hsec
  refine IsAmpleLB.tens_of_forall_isPsEff k X (strHom k X) hp A M hA hM.isLB ?_
  intro Z hZ
  by_cases hZX : (Z : Set X) = Set.univ
  · exact GlobalTheory.T.isPseudoEffective_reducedUniv_of_section_pow k X hp M hM.isLB r hr hs Z hZX
  · exact GlobalTheory.T.isPsEff_pull_reduced_closed_of_dim_le k d hd X hp M hM Z hZ (_root_.GlobalTheory.topologicalKrullDim_le_of_isClosed_ne_univ X d hX (Z : Set X) Z.isClosed hZX)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefOfSemiPosGeneratedBySmallSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenNef

theorem isNef_of_gen_small : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (n : ℕ) (s : Fin n → M.B.Sec), M.SemiPos D → (∀ i, s i ∈ M.smallSec) → (∀ x : X, ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.IsNef D := by
  intro _ k _ X _ p D hX M n s hsp hsm hs
  have hcov : ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) = ⊤ :=
    top_le_iff.1 fun x _ =>
      have ⟨i, hi⟩ := hs x
      Opens.mem_iSup.2 ⟨i, hi⟩
  exact GlobalTheory.VolBr.Model.isNef_of_small hX M hsp
    (GlobalTheory.TrueGeo.OfLattice.nefFib_of_isGenerated hX M (GlobalTheory.isGenerated_of_finite s hcov))
    fun x => have ⟨i, hi⟩ := hs x; ⟨s i, hsm i, hi⟩

end GlobalTheory.GenNef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedLatticeColumnLatticeMulIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedLattice_columnLattice_mul_iff : ∀ (D : D7) {n : ℕ} (γ B : GL (Fin n) D.host.E), ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (γ * B)) ↔
      (γ⁻¹).1.map (eToEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) := by
  first | exact @GlobalTheory.LatMulAd.mem_hatL_colLat_mul | exact GlobalTheory.LatMulAd.mem_hatL_colLat_mul | (intros; apply GlobalTheory.LatMulAd.mem_hatL_colLat_mul <;> assumption)
end

