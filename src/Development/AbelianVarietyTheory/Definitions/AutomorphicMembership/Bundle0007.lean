module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0014
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0007
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
section
noncomputable section

namespace GlobalTheory.Mem.SJ

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Bs : DefBase D.what₂.LL} {A : DefAmb Bs}

structure Read (D : D7) {Bs : DefBase D.what₂.LL} {A : DefAmb Bs} (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) where

  wU : D.what₂.Word → (fc X.zs).Dc.Mem

  eNu : ∀ u, (Fin ((fc X.zs).Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V

  eRR : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V

  jV : (Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb D.what₂.mu0

  v0 : Bs.v0 = InfinitePlace.mk D.what₂.embLL

  twist : ∀ a, Bs.v0.embedding a = cj s (D.what₂.embLL a)

variable {X : CxData A} {fc : DefSub A → DefFace Bs} {s : Bool}

structure Seam (R : Read D X fc s) (cr : Crd A fc) where

  cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc X.zs).Dc.a (R.wU u)) → ℂ)

  cF : (Fin ((fc X.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0

  eR : D.what₂.EE →ₛₗ[cj s] X.EE

  cφ_eq : ∀ u x, (cφ u).symm (cpt D.what₂.embLL x) = D.jN u (R.eNu u x)

  cF_eq : ∀ y, cF (cpt D.what₂.embLL y) = R.jV y

  eR_eq : ∀ y, eR (D.jEE (R.eRR y)) = X.iC cr true Bs.μ0 (cpt Bs.v0.embedding y)

namespace Read

variable (R : Read D X fc s)

def DcPt : Prop :=
  ∀ u x y, D.what₂.embLL ((fc X.zs).Dc.Pt (R.wU u) Bs.μ0 x y) = D.what₂.perCol u D.what₂.mu0 (D.jN u (R.eNu u x)) (R.jV y)

def ReadingFormsSpanGoodSubspace : Prop := Submodule.span ℂ (Set.range R.jV) = D.what₂.V0 D.what₂.mu0

def IotaRd (cr : Crd A fc) : Prop :=
  ∀ y, D.what₂.iota D.what₂.mu0 (R.jV y) =
    D.jEE (R.eRR ((X.rowMat cr true Bs.μ0).mulVec (((lv (fc X.zs) true).Pq Bs.μ0).mulVec y)))

def NuTie : Prop := ∀ u, ∃ L, HLatTie (D.div.Nu u) L ((fc X.zs).Dc.Xc (R.wU u)) (R.eNu u)

def RRTie (cr : Crd A fc) : Prop := ∃ L, HLatTie D.div.RR L (X.XE cr true) R.eRR

end Read

structure CxFacts (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc)
    (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t) : Prop where

  wf : (fc X.zs).Df1.WF

  h2 : X.H2 cr true

  pos : X.H4pos

  theta : ∀ y, X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 y)) =
    X.Θ Bs.μ0 (X.jR Bs.μ0 (cr.toR X.zs true Bs.μ0 (((fc X.zs).Df1.Pq Bs.μ0).mulVec y)))

def cjv (s : Bool) {n : ℕ} (x : Fin n → ℂ) : Fin n → ℂ := fun i => cj s (x i)

namespace Seam

variable {R : Read D X fc s} {cr : Crd A fc} (M : Seam R cr)

def ChainTie : Prop :=
  ∀ u (x : Fin ((fc X.zs).Dc.a (R.wU u)) → D.what₂.LL) (y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL),
    D.what₂.perCol u D.what₂.mu0 ((M.cφ u).symm (cpt D.what₂.embLL x)) (M.cF (cpt D.what₂.embLL y)) =
      D.what₂.embLL ((fc X.zs).Dc.Pt (R.wU u) Bs.μ0 x y)

def GoodPartHasComplexCoordinates : Prop := D.what₂.V0 D.what₂.mu0 ≤ LinearMap.range M.cF

def RowTie (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t) : Prop :=
  (∀ F, M.eR F ∈ X.EEl true) ∧ (∀ e ∈ X.EEl true, ∃ F, M.eR F = e) ∧ (∃ c : ℝ, 0 < c ∧ ∀ F, ‖M.eR F‖ = c * ‖F‖) ∧
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL,
      X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 y)) = lam • M.eR (D.what₂.iota D.what₂.mu0 (M.cF (cpt D.what₂.embLL y)))

def ColNorm : Prop :=
  ∀ u, ∃ c : ℝ, 0 < c ∧ ∀ φ : D.what₂.Mu u, Formalism.DivisionValues.fnorm ((fc X.zs).Dc.Xc (R.wU u) Bs.v0) (cjv s (M.cφ u φ)) = c * ‖φ‖

end Seam

section Extend

theorem lin_cpt_semilinear {K E : Type} [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] E) (x : Fin n → K) :
    lin (fun k => j (Pi.single k 1)) (cpt σ x) = j x := by
  have hx : x = ∑ k, x k • (Pi.single k (1 : K) : Fin n → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin, cpt, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ]

theorem lin_bijective_of_form {K V E ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup E] [Module ℂ E]
    (σ : K →+* ℂ) {n : ℕ} (j : V →ₛₗ[σ] E) (b : Module.Basis ι K V) (e : (Fin n → K) ≃ₗ[K] V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range (fun i => j (b i))) = ⊤) :
    Function.Bijective (lin fun k => j (e (Pi.single k 1))) := by
  classical
  have hcpt : ∀ y, lin (fun k => j (e (Pi.single k 1))) (cpt σ y) = j (e y) := fun y =>
    lin_cpt_semilinear σ (j.comp e.toLinearMap) y
  have hsurj : Function.Surjective (lin fun k => j (e (Pi.single k 1))) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine LinearMap.mem_range.2 ⟨cpt σ (e.symm (b i)), ?_⟩
    rw [hcpt, LinearEquiv.apply_symm_apply]
  have : Module.Finite K V := Module.Finite.equiv e
  have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  let bE := Module.Basis.mk hb.1 hb.2.ge
  have : FiniteDimensional ℂ E := Module.Finite.of_basis bE
  have hdim : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ E := by
    rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis bE, ← Module.finrank_eq_card_basis b,
      ← e.finrank_eq, Module.finrank_fin_fun]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj, hsurj⟩

namespace Read

variable (R : Read D X fc s)


end Read

end Extend

section Untwisted

variable {R : Read D X fc false} {cr : Crd A fc} (M : Seam R cr)

namespace Seam

end Seam

end Untwisted

section OfTie

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}

variable (F : Face D A) (X : CxData A.fam.amb) {S₀ : IndefData (A.side F.P0 F.ψ0 X.zs)} {X₀ : BaseLevelRowSide D}
  (I : DivisionCompatibilityData D A F.P0 F.ψ0 F.P1 F.ψ1 X.zs S₀ (X.data F.cr true) X₀ (F.Dc X.zs))

variable {Sp : SPer (F.Dc X.zs)} {C : ColData (F.Dc X.zs) Sp (X.data F.cr true)}
  {NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin ((F.Dc X.zs).a u) → D.what₂.LL)}

end OfTie

section Place

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)

end Block

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} (F : Face D A)

variable (X : CxData A.fam.amb) {n : ℕ}

end Place

end GlobalTheory.Mem.SJ

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
section
noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem map_scalar {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (u : Rˣ) :
    GeneralLinearGroup.map p (GeneralLinearGroup.scalar (Fin a) u) =
      GeneralLinearGroup.scalar (Fin a) (Units.map p.toMonoidHom u) := by
  ext i j
  change p (Matrix.diagonal (fun _ => (u : R)) i j) = Matrix.diagonal (fun _ => p u) i j
  simp [Matrix.diagonal_apply, apply_ite p]

theorem cornerGL_scalar {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (u : Rˣ) :
    cornerGL a s (GeneralLinearGroup.scalar (Fin a) u) =
      GeneralLinearGroup.scalar (Fin a) (Units.map (corner s) u) := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) +
    s (Matrix.diagonal (fun _ => (u : R)) i j) = Matrix.diagonal (fun _ => 1 - s 1 + s u) i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem scalar_comm {R : Type} [CommRing R] (u : Rˣ) (g : GL (Fin a) R) :
    GeneralLinearGroup.scalar (Fin a) u * g = g * GeneralLinearGroup.scalar (Fin a) u :=
  Units.ext (Matrix.scalar_commute (u : R) (fun _ => Commute.all _ _) g.val).eq

theorem infId_mul_finId (z : Ideles E) :
    infId E (Units.map (pInf E).toMonoidHom z) * finId E (Units.map (pFin E).toMonoidHom z) = z := by
  have h := congrArg GeneralLinearGroup.det (infGL_mul_finGL (GeneralLinearGroup.scalar (Fin 1) z))
  rw [map_mul, det_infGL, det_finGL, map_scalar, map_scalar] at h
  exact (congrArg₂ (fun x y => infId E x * finId E y) (CG.det_oneByOne _) (CG.det_oneByOne _)).symm.trans
    (h.trans (CG.det_oneByOne z))

namespace CuspSub

variable {π π' : CuspSub E a} {ω ω' : HChar E}


variable (π) in
def HasCentral (ω : HChar E) : Prop :=
  ∀ z : Ideles E, ∀ φ ∈ π.V, rt E a (GeneralLinearGroup.scalar (Fin a) z) φ = ((ω.1 z : ℂˣ) : ℂ) • φ

theorem hasCentral_iff : π.HasCentral ω ↔ π.HasCentChar ω := by
  refine ⟨fun h u φ => Subtype.ext ?_, fun h => ?_⟩
  · exact (congrArg (fun g => rt E a g φ.1) (cornerGL_scalar (sFin E) u)).trans (h (finId E u) φ.1 φ.2)
  have hf : ∀ u, ∀ φ ∈ π.V, rt E a (GeneralLinearGroup.scalar (Fin a) (finId E u)) φ =
      ((ω.1 (finId E u) : ℂˣ) : ℂ) • φ := fun u φ hφ =>
    (congrArg (fun g => rt E a g φ) (cornerGL_scalar (sFin E) u)).symm.trans (congrArg Subtype.val (h u ⟨φ, hφ⟩))
  have hi : ∀ y, ∀ φ ∈ π.V, rt E a (GeneralLinearGroup.scalar (Fin a) (infId E y)) φ =
      ((ω.1 (infId E y) : ℂˣ) : ℂ) • φ := fun y φ hφ => Subtype.ext <| funext fun g => by
    refine congrFun (InfType.denseRange_units.equalizer
      (g := fun y => φ.1 (g * GeneralLinearGroup.scalar (Fin a) (infId E y)))
      (h := fun y => ((ω.1 (infId E y) : ℂˣ) : ℂ) * φ.1 g) ?_
      ((Units.continuous_val.comp (continuous_chiInf ω)).mul continuous_const) (funext fun k => ?_)) y
    · have e : (fun y => φ.1 (g * GeneralLinearGroup.scalar (Fin a) (infId E y))) =
          fun y : (Cinf E)ˣ => chart φ.1 g (toL (GeneralLinearGroup.scalar (Fin a) y).val) := by
        funext y
        rw [chart_val]
        exact congrArg (fun x => φ.1 (g * x)) (cornerGL_scalar (sInf E) y).symm
      rw [e]
      refine (φ.2 g).continuousOn.comp_continuous ?_ fun y => val_mem_invSet _
      exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
    · have e : infId E (Units.map (InfType.diagInf E).toMonoidHom k) = diagUnits E k *
          finId E (Units.map (pFin E).toMonoidHom (diagUnits E k))⁻¹ := by
        rw [map_inv, eq_mul_inv_iff_mul_eq]
        exact infId_mul_finId (diagUnits E k)
      have e2 : GeneralLinearGroup.scalar (Fin a) (diagUnits E k) = ratGL E a (GeneralLinearGroup.scalar (Fin a) k) :=
        (map_scalar _ k).symm
      simp only [Function.comp_apply]
      rw [e, map_mul, map_mul, ω.2.2, one_mul, ← mul_assoc, ← scalar_comm (diagUnits E k), e2, mul_assoc, (π.cusp φ hφ).1.left]
      exact congrFun (congrArg Subtype.val (hf _ φ hφ)) g
  intro z φ hφ
  rw [← infId_mul_finId z, map_mul, map_mul, map_mul, Module.End.mul_apply, hf _ φ hφ, map_smul, hi _ φ hφ, smul_smul,
    Units.val_mul, mul_comm]

theorem HasCentral.unique (h : π.HasCentral ω) (h' : π.HasCentral ω') : ω = ω' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  exact Subtype.ext (MonoidHom.ext fun z => Units.ext (smul_left_injective ℂ h0 ((h z φ hφ).symm.trans (h' z φ hφ))))

theorem HasCentral.twist (h : π.HasCentral ω) (χ : HChar E) : (π.twist χ).HasCentral (ω * χ ^ a) :=
  hasCentral_iff.2 ((hasCentral_iff.1 h).twist χ)

theorem HasCentral.apply (h : π.HasCentral ω) {φ : Sm E a} (hφ : φ ∈ π.V) (z : Ideles E) (g : GA E a) :
    φ.1 (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g := by
  rw [scalar_comm]
  exact congrFun (congrArg Subtype.val (h z φ hφ)) g


variable (π) in
def IsUnitary : Prop := ∃ ω : HChar E, ω.IsUnitary ∧ π.HasCentral ω

theorem HasCentral.isUnitary_iff (h : π.HasCentral ω) : π.IsUnitary ↔ ω.IsUnitary :=
  ⟨fun ⟨_, h1, h2⟩ => h2.unique h ▸ h1, fun h1 => ⟨ω, h1, h⟩⟩

theorem IsUnitary.norm_eq (h : π.IsUnitary) {φ : Sm E a} (hφ : φ ∈ π.V) (z : Ideles E) (g : GA E a) :
    ‖φ.1 (GeneralLinearGroup.scalar (Fin a) z * g)‖ = ‖φ.1 g‖ := by
  obtain ⟨ω, h1, h2⟩ := h
  rw [h2.apply hφ, norm_mul, h1, one_mul]

end CuspSub


omit [_root_.NumberField.IsTotallyComplex E] in
theorem isUnitary_one : (1 : HChar E).IsUnitary := fun _ => norm_one


omit [_root_.NumberField.IsTotallyComplex E] in
theorem isUnitary_pow {χ : HChar E} (h : χ.IsUnitary) (n : ℕ) : (χ ^ n).IsUnitary := by
  induction n with
  | zero => rw [pow_zero]; exact isUnitary_one
  | succ n ih => rw [pow_succ]; exact ih.mul h


namespace CG

variable {π : CG E a} {ω ω' : HChar E}

@[simp] theorem isUnitary_mk (π : CuspSub E a) : (mk π).IsUnitary ↔ π.IsUnitary :=
  exists_congr fun _ => and_congr_right fun _ => CuspSub.hasCentral_iff.symm

theorem HasCentChar.unique (h : π.HasCentChar ω) (h' : π.HasCentChar ω') : ω = ω' := by
  induction π using Quotient.inductionOn with
  | _ π => exact (CuspSub.hasCentral_iff.2 h).unique (CuspSub.hasCentral_iff.2 h')

theorem HasCentChar.isUnitary_iff (h : π.HasCentChar ω) : π.IsUnitary ↔ ω.IsUnitary :=
  ⟨fun ⟨_, h1, h2⟩ => h2.unique h ▸ h1, fun h1 => ⟨ω, h1, h⟩⟩

@[simp] theorem isUnitary_ofChar_iff (χ : HChar E) : (ofChar χ).IsUnitary ↔ χ.IsUnitary :=
  (hasCentChar_ofChar χ).isUnitary_iff

theorem IsUnitary.twist (h : π.IsUnitary) {χ : HChar E} (hχ : χ.IsUnitary) : (π.twist χ).IsUnitary := by
  obtain ⟨ω, h1, h2⟩ := h
  exact ⟨_, h1.mul (isUnitary_pow hχ a), h2.twist χ⟩

@[simp] theorem ofChar_toChar (σ : CG E 1) : ofChar (toChar σ) = σ :=
  Function.rightInverse_invFun (RankOne.ofChar_bijective E).2 σ

theorem isUnitary_toChar_iff (σ : CG E 1) : (toChar σ).IsUnitary ↔ σ.IsUnitary := by
  rw [← isUnitary_ofChar_iff, ofChar_toChar]

theorem IsUnitary.tw (h : π.IsUnitary) {σ : CG E 1} (hσ : σ.IsUnitary) : (π.tw σ).IsUnitary :=
  h.twist ((isUnitary_toChar_iff σ).2 hσ)

end CG


variable (E a) in
abbrev CGu : Type := {π : CG E a // π.IsUnitary}

namespace CGu

variable (π : CGu E a)

def twist (χ : {χ : HChar E // χ.IsUnitary}) : CGu E a := ⟨π.1.twist χ.1, π.2.twist χ.2⟩

def tw (σ : CGu E 1) : CGu E a := ⟨π.1.tw σ.1, π.2.tw σ.2⟩

abbrev infChar (τ : E →+* ℂ) : Multiset ℂ := π.1.infChar τ

abbrev IsRegAlg : Prop := π.1.IsRegAlg

abbrev IsCsd {L : Type} [Field L] [NumberField L] [IsCMField L] (π : CGu L a) : Prop := π.1.IsCsd

def centChar : {χ : HChar E // χ.IsUnitary} := ⟨π.2.choose, π.2.choose_spec.1⟩

theorem hasCentChar_centChar : π.1.HasCentChar π.centChar.1 := π.2.choose_spec.2

theorem centChar_twist (χ : {χ : HChar E // χ.IsUnitary}) : (π.twist χ).centChar.1 = π.centChar.1 * χ.1 ^ a :=
  (π.twist χ).hasCentChar_centChar.unique (π.hasCentChar_centChar.twist χ.1)


variable (E) in
def equivChar : CGu E 1 ≃ {χ : HChar E // χ.IsUnitary} where
  toFun σ := ⟨σ.1.toChar, (CG.isUnitary_toChar_iff _).2 σ.2⟩
  invFun χ := ⟨CG.ofChar χ.1, CG.isUnitary_ofChar χ.2⟩
  left_inv σ := Subtype.ext (CG.ofChar_toChar σ.1)
  right_inv χ := Subtype.ext (CG.toChar_ofChar χ.1)

theorem ofChar_equivChar (σ : CGu E 1) : CG.ofChar (equivChar E σ).1 = σ.1 := CG.ofChar_toChar σ.1

theorem equivChar_tw (σ σ' : CGu E 1) : (equivChar E (σ.tw σ')).1 = (equivChar E σ).1 * (equivChar E σ').1 := by
  apply CG.ofChar_injective
  rw [ofChar_equivChar, ← CG.twist_ofChar, ofChar_equivChar]
  rfl

end CGu

abbrev HostCGu {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (a : ℕ) : Type :=
  haveI := host_isCMField H; CGu H.E a

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MulVecMemLatMap
section
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

section Tri

variable {m : ℕ} {u v : Matrix (Fin m) (Fin m) E}

theorem up_one : IsUp (1 : Matrix (Fin m) (Fin m) E) :=
  fun _ _ => ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq _⟩

def IsStrict (A : Matrix (Fin m) (Fin m) E) : Prop := ∀ i j, j ≤ i → A i j = 0

def simpleSum {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E := ∑ a : Fin r, A a.castSucc a.succ

end Tri

section Frames

variable {σ : E →+* E} {n r : ℕ} {J s : Matrix (Fin n) (Fin n) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

end Frames

section Lattices

variable [NumberField E] {σ : E →+* E} {n r : ℕ} {J s : Matrix (Fin n) (Fin n) E}
  {P P' : Matrix (Fin n) (Fin (r + 1)) E} {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Λ M : Submodule (𝓞 E) (Fin n → E)}





end Lattices

end GlobalTheory.IntTerm
end
end

