module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1047
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorEquivariantDoubleCosetSectionBasePoint
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.TraceBlocks

theorem levOp_secM_apply_self : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G), Function.Injective ι → ∀ (ρ : Representation ℂ H V) (K K' : Subgroup G) (F : G → ℂ), (∀ k ∈ K', ∀ x, F (x * k) = F x) → {q : G ⧸ K' | F q.out ≠ 0}.Finite → ∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G) → {h : H | F (x⁻¹ * ι h * x) ≠ 0}.Finite → ∀ v : V, levOp (rightReg ℂ G V) K K' F LinearMap.id (secM ι ρ K' x v) x = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ((stabCard ι K' x : ℂ))⁻¹ • ∑ᶠ h : H, F (x⁻¹ * ι h * x) • ρ h v := by
  intro G H V _ _ _ _ ι _ ρ K K' F hF hS x _ hT v
  have hout : ∀ y : G, F (y : G ⧸ K').out = F y := by
    intro y
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K' y
    rw [hk, hF _ k.2]
  have hcond : ∀ (q : G ⧸ K') (h : H),
      ((ι h * x)⁻¹ * (x * q.out) ∈ K') ↔ (((x⁻¹ * ι h * x : G) : G ⧸ K') = q) := by
    intro q h
    have e : (ι h * x)⁻¹ * (x * q.out) = (x⁻¹ * ι h * x)⁻¹ * q.out := by group
    rw [e]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.symm
  have hreg : ∀ (g : G) (φ : G → V) (y : G), rightReg ℂ G V g φ y = φ (y * g) := fun _ _ _ => rfl
  have hsec : ∀ y, secM ι ρ K' x v y =
      ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) v := fun _ => rfl
  rw [GlobalTheory.BCT.LevOpTmul.levOp_apply _ K K' F LinearMap.id hS.toFinset (fun q hq => by simpa using hq)]
  rw [finsum_eq_sum_of_support_subset (f := fun h : H => F (x⁻¹ * ι h * x) • ρ h v) (s := hT.toFinset) (fun h hh => by
    rw [Set.Finite.coe_toFinset]
    intro h0; exact hh (by simp only [h0, zero_smul]))]
  simp only [Pi.smul_apply, Finset.sum_apply, LinearMap.id_apply, hreg, hsec]
  congr 1
  have hin : ∀ q ∈ hS.toFinset, (∑ᶠ h : H, if (ι h * x)⁻¹ * (x * q.out) ∈ K' then ρ h else 0) =
      ∑ h ∈ hT.toFinset, if (((x⁻¹ * ι h * x : G) : G ⧸ K') = q) then ρ h else 0 := by
    intro q hq
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq
    rw [finsum_eq_sum_of_support_subset (s := hT.toFinset)]
    · exact Finset.sum_congr rfl fun h _ => by simp only [hcond]
    · intro h hh
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hh
      obtain ⟨hc, _⟩ := hh
      rw [Set.Finite.coe_toFinset]
      show _ ≠ _
      rw [hcond] at hc
      rw [← hout, hc]; exact hq
  rw [Finset.sum_congr rfl fun q hq => by rw [hin q hq]]
  simp only [LinearMap.sum_apply, Finset.sum_apply, ite_apply, LinearMap.zero_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h hh => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hh
  have : ∀ q ∈ hS.toFinset, F q.out • ((stabCard ι K' x : ℂ))⁻¹ • (if (((x⁻¹ * ι h * x : G) : G ⧸ K') = q) then ρ h else 0) v
      = if (((x⁻¹ * ι h * x : G) : G ⧸ K') = q) then ((stabCard ι K' x : ℂ))⁻¹ • F (x⁻¹ * ι h * x) • ρ h v else 0 := by
    intro q _
    split_ifs with e
    · rw [← e, hout, smul_comm]
    · simp only [LinearMap.zero_apply, smul_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  rw [if_pos]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hout]
  exact hh

end GlobalTheory.BCT.TraceBlocks
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorPreservesEquivariantRightInvariant
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

def leftEqv {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G)
    (ρ : Representation ℂ H V) : Submodule ℂ (G → V) where
  carrier := {φ | ∀ h x, φ (ι h * x) = ρ h (φ x)}
  add_mem' := by
    intro a b ha hb h x
    simp only [Pi.add_apply, ha h x, hb h x, map_add (f := _)]
  zero_mem' := fun _ _ => by simp
  smul_mem' := by
    intro c a ha h x
    simp only [Pi.smul_apply, ha h x, map_smul]

theorem eqvM_eq_inf {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G)
    (ρ : Representation ℂ H V) (K : Subgroup G) :
    eqvM ι ρ K = leftEqv ι ρ ⊓ fixed (rightReg ℂ G V) K := by
  ext φ
  simp only [Submodule.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k => ?_⟩
    funext x
    simpa [rightReg, LinearMap.funLeft] using h2 k k.2 x
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk x => ?_⟩
    have := congrFun (h2 ⟨k, hk⟩) x
    simpa [rightReg, LinearMap.funLeft] using this

theorem levOp_rightReg_mem_eqvM : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G) (ρ : Representation ℂ H V) (K K' : Subgroup G) (F : G → ℂ), (∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) → ∀ φ ∈ eqvM ι ρ K', levOp (rightReg ℂ G V) K K' F LinearMap.id φ ∈ eqvM ι ρ K' := by
  intro G H V _ _ _ _ ι ρ K K' F hF φ hφ
  rw [eqvM_eq_inf] at hφ ⊢
  refine levOp_id_mem_inf_fixed (rightReg ℂ G V) K K' F hF (leftEqv ι ρ) ?_ φ hφ
  intro g v hv h x
  simp only [rightReg, LinearMap.funLeft, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply]
  rw [mul_assoc]
  exact hv h (x * g)

end GlobalTheory.BCT.TraceBlocks
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffLocalQuotients
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem le_iff_local : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B : HermLB p, Le B A ↔ ∃ (r : A.B.ι → X.functionFieldˣ) (r' : B.B.ι → X.functionFieldˣ), IsRatSec A.B r ∧ IsRatSec B.B r' ∧ (∀ (x : X) i j, x ∈ A.B.U i → x ∈ B.B.U j → RegAt x ((r i : X.functionField) / (r' j : X.functionField))) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (A.B.U i) → y ∈ ptsIn p σ (B.B.U j) → ‖ratVal ((r i : X.functionField) / (r' j : X.functionField)) y‖ * Real.exp (-((A.φ σ).φ i y - (B.φ σ).φ j y) / 2) ≤ 1 := by
  intro k _ X _ p A B
  have hloc : ∀ (P : Pair p) i j, P.loc 1 (-1) 1 i j = (P.r i : X.functionField) / (P.r' j : X.functionField) := by
    intro P i j
    simp [Pair.loc, div_eq_mul_inv]
  have hexp : ∀ s t : ℝ, -(((1 : ℤ) : ℝ) * s + ((-1 : ℤ) : ℝ) * t) / 2 = -(s - t) / 2 := by
    intro s t
    push_cast
    ring
  constructor
  · rintro ⟨P, rfl, rfl, hH, hnu⟩
    refine ⟨P.r, P.r', P.hr, P.hr', fun x i j hi hj => ?_, fun σ y i j hi hj => ?_⟩
    · rw [← hloc]
      exact hH x i j hi hj
    · have e := hnu σ y
      rw [nu_eq k X p P 1 (-1) 1 hH σ y i j hi hj, hloc, hexp] at e
      exact e
  · rintro ⟨r, r', hr, hr', hreg, hnu⟩
    refine ⟨⟨A, B, r, r', hr, hr'⟩, rfl, rfl, fun x i j hi hj => ?_, fun σ y => ?_⟩
    · rw [hloc]
      exact hreg x i j hi hj
    · rw [Pair.nu, hloc, hexp]
      exact hnu σ y _ _ (mem_pick _ y) (mem_pick _ y)

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairSectionsGoodShiftSecondBundleNormPair
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem nu_shiftA {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (u : ℝ)
    (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u)) := by
  change ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
      Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * ((P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y + 2 * u)) / 2) = _
  rw [Pair.nu, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem Bl_subset_shiftA {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) {u : ℝ}
    (hu : 0 ≤ u) (a b : ℤ) (hb : 0 ≤ b) {R : ℝ} {f : X.functionField} (hf : f ∈ P.Bl a b R) :
    f ∈ (shiftA P u).Bl a b R := by
  refine ⟨hf.1, fun σ y => ?_⟩
  rw [nu_shiftA]
  have h1 : Real.exp (-(b * u)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : (0 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith)
  have h0 : 0 ≤ P.nu a b σ y f := by unfold Pair.nu; positivity
  have h2 : R ≥ P.nu a b σ y f := hf.2 σ y
  nlinarith [Real.exp_pos (-(b * u))]

theorem good_shiftA : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (b : ℕ) (s t : X.functionField) (u : ℝ), 0 ≤ u → P.Good D b s t → (shiftA P u).Good D b s t := by
  intro k _ X _ p D hX P b s t u hu h
  exact
    { ample := h.ample
      nef := GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX P.A u hu h.nef
      pos := h.pos
      s_mem := Bl_subset_shiftA P hu 0 1 zero_le_one h.s_mem
      s_ne := h.s_ne
      t_mem := Bl_subset_shiftA P hu (-1) b (Int.natCast_nonneg b) h.t_mem
      t_ne := h.t_ne
      reg := h.reg }

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspFormOfExtremalVectorMultiplicity
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem holForm_zCusp_of_mem_mult : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, HolForm θ M w J χ (T v) ∧ ZCusp V (T v) := by
  intro hP D θ V S M w v hθ hM hw hv J χ T hT
  have h := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 hT
  have hd := GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ (h.aut v) (h.cusp v)
  have hh := _root_.GlobalTheory.MultHol.holAd_of_isMultMap D θ V S M w v hθ hM hw hv J χ T h
  exact ⟨⟨(h.aut v).toIsAutFun, hd.bounded, h.lev v, hh⟩,
    _root_.GlobalTheory.HolDict.ZDecay.zCusp_of_rapidDecay D θ V S M w hθ hM _ (h.aut v).toIsAutFun hh hd⟩

end GlobalTheory.HolDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSupportHermitianDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.StdReps

section General

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_nat_smul_mem (L L' : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hsp : Submodule.span E (L' : Set (Fin n → E)) = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∀ x ∈ L, (c : E) • x ∈ L' := by
  first
  | exact @_root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le
  | exact _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le
  | (apply _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le ..)

theorem fg_colLat (B : GL (Fin n) E) : (colLat B).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem span_colLat (B : GL (Fin n) E) : Submodule.span E (colLat B : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ j, ((B⁻¹).1 *ᵥ x) j • (fun a : Fin n => (B : Matrix (Fin n) (Fin n) E) a j) := by
    have e : x = B.1 *ᵥ ((B⁻¹).1 *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    conv_lhs => rw [e]
    funext a
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hx]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Submodule.subset_span ⟨j, rfl⟩

end General

variable {D : D7}

def stabGL {R : Type} [CommRing R] {m : ℕ} (H : Set (Fin m → R)) : Subgroup (GL (Fin m) R) where
  carrier := {g | ∀ v, v ∈ H ↔ g.1 *ᵥ v ∈ H}
  one_mem' := fun v => by rw [Units.val_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb v => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb v).trans (ha _)
  inv_mem' := fun {a} ha v => by
    have := ha ((a⁻¹).1 *ᵥ v)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm

def stabG (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Subgroup (GA D V) :=
  (stabGL (Formalism.L2.Herm.hatL (F := D.host.F) M : Set (Fin V.rank → Formalism.IndefR.Lev.EAf D))).comap (Formalism.IndefR.Lev.finE V)


set_option maxHeartbeats 1000000 in
theorem mulVec_mem_of_finCong (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ) (hc : 0 < c)
    (h1 : ∀ x ∈ M, (c : D.host.E) • x ∈ GlobalTheory.Member.latC V)
    (h2 : ∀ x ∈ GlobalTheory.Member.latC V, (c : D.host.E) • x ∈ M) (a : GA D V) (ha : GlobalTheory.Member.FinCong V (c * c) a) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M,
      (Formalism.IndefR.Lev.finE V a).1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M := by
  have hl := (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hcong : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.Member.latC V),
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.Member.latC V),
        (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (c * c) • y := by
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap _ _ _ ha
  intro z hz
  obtain ⟨y, hy, e⟩ := hcong _ (GlobalTheory.LevSplit.hatL_smul _ _ c h1 z hz)
  have hcE : IsUnit (c : D.host.E) := (Nat.cast_ne_zero.2 hc.ne').isUnit
  have hu : IsUnit (c : Formalism.IndefR.Lev.EAf D) := by
    have := hcE.map (eToEAf D)
    rwa [map_natCast] at this
  have e2 : (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (c : Formalism.IndefR.Lev.EAf D) • y := by
    refine (hu.smul_left_cancel).1 ?_
    rw [smul_sub, ← Matrix.mulVec_smul, e, ← Nat.cast_smul_eq_nsmul (Formalism.IndefR.Lev.EAf D), Nat.cast_mul, mul_smul]
  rw [sub_eq_iff_eq_add'] at e2
  rw [e2]
  exact Submodule.add_mem _ hz (GlobalTheory.LevSplit.hatL_smul _ _ c h2 y hy)


set_option maxHeartbeats 1000000 in
theorem mem_stabG_of_finCong (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ) (hc : 0 < c)
    (h1 : ∀ x ∈ M, (c : D.host.E) • x ∈ GlobalTheory.Member.latC V)
    (h2 : ∀ x ∈ GlobalTheory.Member.latC V, (c : D.host.E) • x ∈ M) (a : GA D V) (ha : GlobalTheory.Member.FinCong V (c * c) a) :
    a ∈ stabG V M := by
  intro v
  refine ⟨mulVec_mem_of_finCong V M c hc h1 h2 a ha v, fun hv => ?_⟩
  have := mulVec_mem_of_finCong V M c hc h1 h2 a⁻¹ (GlobalTheory.Member.PrincLevel.finCong_inv ha) _ hv
  rwa [map_inv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this


set_option maxHeartbeats 4000000 in
theorem exists_rep_std : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (S : Finset ℕ), (∀ q ∈ S, q.Prime) →
    ∀ x : GA D V, x ∈ GfC V →
    ∃ (γ : GL (Fin V.rank) D.host.E) (h k : GA D V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram ∧ h ∈ GfC V ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) ∧
      k ∈ GfC V ∧ (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) ∧
      (Formalism.IndefR.Lev.finE V x).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (Formalism.IndefR.Lev.finE V k).1 := by
  intro D V fr S hS x hx
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨c1, hc1, h1⟩ := exists_nat_smul_mem (colLat fr) (GlobalTheory.Member.latC V) (fg_colLat fr) hsp
  obtain ⟨c2, hc2, h2⟩ := exists_nat_smul_mem (GlobalTheory.Member.latC V) (colLat fr) hfg (span_colLat fr)
  have h1' : ∀ y ∈ colLat fr, ((c1 * c2 : ℕ) : D.host.E) • y ∈ GlobalTheory.Member.latC V := fun y hy => by
    rw [Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul D.host.E c2]
    exact (GlobalTheory.Member.latC V).toAddSubmonoid.nsmul_mem (h1 y hy) c2
  have h2' : ∀ y ∈ GlobalTheory.Member.latC V, ((c1 * c2 : ℕ) : D.host.E) • y ∈ colLat fr := fun y hy => by
    rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul D.host.E c1]
    exact (colLat fr).toAddSubmonoid.nsmul_mem (h2 y hy) c1
  have hc : 0 < c1 * c2 := Nat.mul_pos hc1 hc2
  let J' : Subgroup (Formalism.IndefR.Bridge.Gf V) := (GfC V ⊓ stabG V (colLat fr)).map (finHom V).rangeRestrict
  have hK : ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V ((c1 * c2) * (c1 * c2)) k → Formalism.IndefR.FWT.fin V k ∈ J' :=
    fun k hk hck => ⟨k, ⟨hk, mem_stabG_of_finCong V (colLat fr) _ hc h1' h2' k hck⟩, rfl⟩
  have hbad : 0 < ∏ q ∈ S, q := Finset.prod_pos fun q hq => (hS q hq).pos
  obtain ⟨h, ⟨hh, hs⟩, γ, k, e⟩ :=
    GlobalTheory.SplitReps.exists_split_rep V (Nat.mul_pos hc hc) hK hbad (Formalism.IndefR.FWT.fin V x)
  obtain ⟨k0, ⟨hk0, hk0s⟩, hk0e⟩ := Subgroup.mem_map.1 k.2
  obtain ⟨-, e0, P, he0, hP, hsupp⟩ := GlobalTheory.SplitReps.splitOffBad_of_suppSplit V _ h hh hs
  obtain ⟨γE, hU, hγ⟩ := γ.2
  have hm : matHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γE := hγ.symm
  have hfγ : finHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE := by
    rw [finHom, MonoidHom.comp_apply, hm]
    exact GlobalTheory.HLatMove.bc_map_bc_inclR _ _
  have ef : finHom V x = finHom V γ.1 * finHom V h * finHom V k0 := by
    have := congrArg Subtype.val e
    rw [← hk0e] at this
    exact this
  refine ⟨γE, h, k0, hU, hh, ⟨P, e0, he0, hsupp, fun w hw q hq hqw => hP w hw ?_⟩, hk0, hk0s, ?_⟩
  · obtain ⟨m, hm'⟩ := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq
    rw [hm', Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hqw
  · have eE : Formalism.IndefR.Lev.finE V x = Formalism.IndefR.Lev.finE V γ.1 * Formalism.IndefR.Lev.finE V h * Formalism.IndefR.Lev.finE V k0 := by
      simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, ef, map_mul]
    have eγ : (Formalism.IndefR.Lev.finE V γ.1).1 = γE.1.map (eToEAf D) := by
      simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, hfγ]
      ext i j
      rfl
    rw [eE, Units.val_mul, Units.val_mul, eγ]

end GlobalTheory.FunObj.StdReps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFiniteSumTopForms
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

private theorem isTopForm_hasInt_finset_sum {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n))
    (he : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source))
    (hc : ∀ y, ∃ i, y ∈ (e i).source) {S : Set Y} (hS : MeasurableSet S) {ι : Type}
    {d : ι → κ → Y → ℝ} {t : ι → ℝ} (hd : ∀ a, IsTopForm e (d a) S) (ht : ∀ a, HasInt e (d a) S (t a))
    (s : Finset ι) :
    IsTopForm e (fun i y => ∑ a ∈ s, d a i y) S ∧ HasInt e (fun i y => ∑ a ∈ s, d a i y) S (∑ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨⟨fun _ _ _ _ _ _ => by simp, fun _ => aemeasurable_const⟩, _root_.GlobalTheory.GoodTop.hasInt_zero e S⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    obtain ⟨hF, hI⟩ := ih
    refine ⟨⟨fun i j y hy hi hj => ?_, fun i => ((hd a).meas i).add (hF.meas i)⟩,
      _root_.GlobalTheory.GoodTop.hasInt_add e he hc hS (hd a) hF (ht a) hI⟩
    rw [(hd a).trans i j y hy hi hj, hF.trans i j y hy hi hj]
    ring

theorem hasInt_sum : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)),
    (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) →
    (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {ι : Type} [Fintype ι]
    {d : ι → κ → Y → ℝ} {t : ι → ℝ}, (∀ a, IsTopForm e (d a) S) → (∀ a, HasInt e (d a) S (t a)) →
    HasInt e (fun i y => ∑ a, d a i y) S (∑ a, t a) := by
  intro n Y κ _ _ _ _ e he hc S hS ι _ d t hd ht
  exact (isTopForm_hasInt_finset_sum e he hc hS hd ht Finset.univ).2

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSheafEqSumLengthMulCycleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_sheaf_eq_sum_length_mul_cycle : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (ι : Type) [Fintype ι] (P : ι → LB X), (∀ i, (P i).IsLB) → ∀ (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F], GlobalTheory.QCoh.suppDim F ≤ (Fintype.card ι : ℕ) → ∀ S : Finset X, (∀ w ∈ GlobalTheory.QCoh.support F, topologicalKrullDim (closure ({w} : Set X)) = (Fintype.card ι : ℕ) → w ∈ S) → interNum κ F P = ∑ w ∈ S, ((Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :)).toNat : ℤ) * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  first | exact @GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed | exact GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed | (intros; apply GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundlePullbackFieldExtensionIffStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBigLineBundle_pullback_fieldExtension_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q → topologicalKrullDim X = topologicalKrullDim Y → ∀ L : LB Y, L.IsLB → ((letI := algebraΓOfHom q; IsBig E (L.pull π)) ↔ (letI := algebraΓOfHom p; IsBig k L)) := by
  first | exact @GlobalTheory.BigFieldChange.isBig_pull_iff | exact GlobalTheory.BigFieldChange.isBig_pull_iff | (intros; apply GlobalTheory.BigFieldChange.isBig_pull_iff <;> assumption)
end

