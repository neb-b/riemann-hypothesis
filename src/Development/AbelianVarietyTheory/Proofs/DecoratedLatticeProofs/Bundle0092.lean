module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LocalPointData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalFunction
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.CuspRep.ParLaws GlobalTheory.SatakeFlip

namespace GlobalTheory.BorelSphExist

section Char

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}


variable (k) in
def unrBorel (α : Fin N → ℂˣ) : borel k (Fin N) →* ℂˣ :=
  ((torusChar fun i => SmGL.unrChar k (α i)).comp (leviTorus k (Fin N)).symm.toMonoidHom).comp
    (leviProj k (points (Fin N)))

theorem unrBorel_apply (α : Fin N → ℂˣ) (b : borel k (Fin N)) :
    unrBorel k α b = ∏ i : Fin N, α i ^ ord k (diagU b i) :=
  torusChar_apply _ _

theorem unrBorel_eq_one (α : Fin N → ℂˣ) (b : borel k (Fin N)) (hb : b.1 ∈ KO k (Fin N)) :
    unrBorel k α b = 1 := by
  rw [unrBorel_apply]
  refine Finset.prod_eq_one fun i _ => ?_
  obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff _).1 hb
  have h3 := congrArg (valuation k) (inv_diag_mul b.2 i)
  rw [map_mul, map_one] at h3
  have a1 : valuation k (b.1.val i i) ≤ 1 := h1 i i
  have a2 : valuation k ((b.1⁻¹).val i i) ≤ 1 := h2 i i
  have h : valuation k (diagU b i : k) = 1 := by
    rw [val_diagU]
    exact le_antisymm a1 (h3.ge.trans (mul_le_of_le_one_left' a2))
  rw [ord_eq_zero h, zpow_zero]

end Char

theorem exists_isBorelSph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (γ : Fin N → ℂ), (∀ i, γ i ≠ 0) →
    ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k γ ψ := by
  intro k _ _ _ _ N γ hγ
  let α : Fin N → ℂˣ := fun i => Units.mk0 (γ i) (hγ i)
  obtain ⟨φ, h1, h2, h3⟩ := exists_fun (borel k (Fin N)) (KO k (Fin N)) (unrBorel k α) (fun g => by
    obtain ⟨b, hb, x, hx, e⟩ := iwasawa_blockTriangular k (Fin N) Fin.val g
    exact ⟨⟨b, (mem_borel _).2 hb⟩, x, hx, e⟩) (unrBorel_eq_one α)
  refine ⟨φ, fun g x hx => h3 g x hx, fun b hb t ht => ?_⟩
  have hφ := h2 ⟨b, hb⟩ 1
  rw [mul_one, h1, mul_one] at hφ
  rw [hφ, unrBorel_apply, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hd : diagU ⟨b, hb⟩ i = t i := Units.ext ((val_diagU _ i).trans (ht i))
  rw [hd, Units.val_zpow_eq_zpow_val]
  rfl

end GlobalTheory.BorelSphExist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactIntegralUnitaryFinitePart
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.IntUnitCpt

open Formalism.MainNotions.LeviCoordinates


open Classical in
def red {E : Type} [Field E] [NumberField E] {n : ℕ} (M : ℕ) (A : Matrix (Fin n) (Fin n) E) :
    Fin n → Fin n → (𝓞 E ⧸ Ideal.span {(M : 𝓞 E)}) := fun i j =>
  if h : IsIntegral ℤ (A i j) then Ideal.Quotient.mk _ ⟨A i j, h⟩ else 0

theorem sub_of_red {E : Type} [Field E] [NumberField E] {n : ℕ} (M : ℕ) {A B : Matrix (Fin n) (Fin n) E}
    (hA : ∀ i j, IsIntegral ℤ (A i j)) (hB : ∀ i j, IsIntegral ℤ (B i j)) (h : red M A = red M B) :
    ∀ i j, ∃ b : E, IsIntegral ℤ b ∧ (A - B) i j = (M : E) * b := by
  intro i j
  have e := congrFun (congrFun h i) j
  simp only [red, dif_pos (hA i j), dif_pos (hB i j)] at e
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 e)
  clear e
  refine ⟨b, RingOfIntegers.isIntegral_coe b, ?_⟩
  have := congrArg (fun z : 𝓞 E => (z : E)) hb
  simp only [map_mul, map_natCast, map_sub] at this
  rw [Matrix.sub_apply, mul_comm]
  exact this.symm

theorem mul_cong {E : Type} [Field E] [NumberField E] {n : ℕ} (M : ℕ) {C D : Matrix (Fin n) (Fin n) E}
    (hC : ∀ i j, IsIntegral ℤ (C i j)) (hD : ∀ i j, ∃ b : E, IsIntegral ℤ b ∧ D i j = (M : E) * b) :
    ∀ i j, ∃ a : E, IsIntegral ℤ a ∧ (C * D) i j = (M : E) * a := by
  intro i j
  choose b hb hb' using hD
  refine ⟨∑ k, C i k * b k j, IsIntegral.sum _ fun k _ => (hC i k).mul (hb k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hb' k j]; ring

theorem kset_nhds (I : AutInst) : I.Kset ∈ 𝓝 (1 : I.Gf) := by
  have ho := I.topf_open 1 le_rfl
  refine Filter.mem_of_superset (ho.mem_nhds ?_) fun x hx => hx.1
  refine ⟨(Formalism.UG.stabGL _).one_mem, fun y hy => ⟨0, Submodule.zero_mem _, by simp⟩⟩

end GlobalTheory.IntUnitCpt

namespace GlobalTheory.IntUnitCpt

def fp (I : AutInst) (γ : GL (Fin I.n) I.E) (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) : I.Gf :=
  ⟨Formalism.UG.bc (Formalism.UG.inclE (F := I.F) (Af I.F)) γ,
    Formalism.UG.Final.RatPtsLe I.F I.E (Fin I.n) I.cm.sig I.J (Af I.F) (Subgroup.mem_map_of_mem _ hγ)⟩

theorem fp_mul (I : AutInst) {γ δ : GL (Fin I.n) I.E} (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (hδ : δ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) :
    fp I (γ⁻¹ * δ) (mul_mem (inv_mem hγ) hδ) = (fp I γ hγ)⁻¹ * fp I δ hδ := by
  apply Subtype.ext
  simp [fp, map_mul, map_inv]

theorem eq_of_real (I : AutInst) (v : InfinitePlace I.F) {A B : Matrix (Fin I.n) (Fin I.n) I.E}
    (h : (I.P v)⁻¹ * A.map (I.φ v) * I.P v = (I.P v)⁻¹ * B.map (I.φ v) * I.P v) : A = B := by
  have h2 : A.map (I.φ v) = B.map (I.φ v) := by
    have := congrArg (fun X => I.P v * X * (I.P v)⁻¹) h
    have hp := Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv I v
    simp only [← Matrix.mul_assoc, hp, Matrix.one_mul] at this
    simpa only [Matrix.mul_assoc, hp, Matrix.mul_one] using this
  ext i j
  exact (I.φ v).injective (congrFun (congrFun h2 i) j)

end GlobalTheory.IntUnitCpt

namespace GlobalTheory.IntUnitCpt

theorem intUnit_compact : ∀ I : AutInst, ∃ K : Set I.Gf, IsCompact K ∧ ∀ γ : GL (Fin I.n) I.E,
    γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) →
    (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) →
    ∃ x ∈ I.GFset, x.2 ∈ K ∧ ∀ v, uMat (x.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
  intro I
  classical
  obtain ⟨M, hM, hcong⟩ := CompanionTheory.D.gk.RF.congruence_subgroup_compact_open I I.Kset (kset_nhds I)
  let T : Set (GL (Fin I.n) I.E) := {γ | γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
    (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧
    ∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)}
  haveI : Finite (𝓞 I.E ⧸ Ideal.span {(M : 𝓞 I.E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (Nat.one_le_iff_ne_zero.1 hM))
  let Kq : (Fin I.n → Fin I.n → (𝓞 I.E ⧸ Ideal.span {(M : 𝓞 I.E)})) → Set I.Gf := fun q =>
    if h : ∃ γ, γ ∈ T ∧ red M (γ : Matrix (Fin I.n) (Fin I.n) I.E) = q then
      (fun k => fp I h.choose h.choose_spec.1.1 * k) '' I.Kset else ∅
  refine ⟨⋃ q, Kq q, isCompact_iUnion fun q => ?_, fun γ hγ hi hi' => ?_⟩
  · simp only [Kq]
    split_ifs
    · exact (Formalism.L2.SG.Closed.AutKCompact_holds I).image (continuous_const_mul _)
    · exact isCompact_empty
  · have hex : ∃ γ', γ' ∈ T ∧ red M (γ' : Matrix (Fin I.n) (Fin I.n) I.E) = red M (γ : Matrix (Fin I.n) (Fin I.n) I.E) :=
      ⟨γ, ⟨hγ, hi, hi'⟩, rfl⟩
    refine ⟨(fun v => Formalism.L2.S.S7.DensRat.ratReal I γ hγ v, fp I γ hγ), ⟨γ, hγ, fun v => rfl, rfl⟩,
      Set.mem_iUnion.2 ⟨red M (γ : Matrix (Fin I.n) (Fin I.n) I.E), ?_⟩, fun v => rfl⟩
    simp only [Kq, dif_pos hex]
    obtain ⟨hT', hr⟩ := hex.choose_spec
    set γ' := hex.choose with hγ'def
    refine ⟨(fp I γ' hT'.1)⁻¹ * fp I γ hγ, ?_, mul_inv_cancel_left _ _⟩
    have hδ : γ'⁻¹ * γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := mul_mem (inv_mem hT'.1) hγ
    have hsub := sub_of_red M hT'.2.1 hi hr
    have c1 : CompanionTheory.D.gk.RF.Cong I M ((γ'⁻¹ * γ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) := by
      have e : ((γ'⁻¹ * γ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) - 1 =
          ((γ'⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *
            ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - (γ' : Matrix (Fin I.n) (Fin I.n) I.E)) := by
        rw [Matrix.mul_sub, Units.val_mul, ← Units.val_mul γ'⁻¹ γ', inv_mul_cancel, Units.val_one]
      intro i j
      rw [e]
      refine mul_cong M hT'.2.2 (fun k l => ?_) i j
      obtain ⟨b, hb, hb'⟩ := hsub k l
      exact ⟨-b, hb.neg, by rw [Matrix.sub_apply] at hb' ⊢; rw [← neg_sub, hb']; ring⟩
    have c2 : CompanionTheory.D.gk.RF.Cong I M (((γ'⁻¹ * γ)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) := by
      have e : (((γ'⁻¹ * γ)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) - 1 =
          ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *
            ((γ' : Matrix (Fin I.n) (Fin I.n) I.E) - (γ : Matrix (Fin I.n) (Fin I.n) I.E)) := by
        rw [_root_.mul_inv_rev, inv_inv, Matrix.mul_sub, Units.val_mul, ← Units.val_mul γ⁻¹ γ, inv_mul_cancel, Units.val_one]
      intro i j
      rw [e]
      refine mul_cong M hi' (fun k l => ?_) i j
      obtain ⟨b, hb, hb'⟩ := hsub k l
      exact ⟨b, hb, by rw [Matrix.sub_apply] at hb' ⊢; exact hb'⟩
    obtain ⟨x, hxK, γ₀, hγ₀, hreal, hfin⟩ := hcong (fun v => Formalism.L2.S.S7.DensRat.ratReal I (γ'⁻¹ * γ) hδ v)
      ⟨γ'⁻¹ * γ, ⟨hδ, c1, c2⟩, fun v => rfl⟩
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    have h0 : γ₀ = γ'⁻¹ * γ := Units.ext (eq_of_real I v (hreal v).symm)
    have hx : x = fp I (γ'⁻¹ * γ) hδ := by
      apply Subtype.ext; apply Units.ext
      exact hfin.trans (by rw [h0]; rfl)
    rw [← fp_mul I hT'.1 hγ, ← hx]
    exact hxK

end GlobalTheory.IntUnitCpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasis
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlEmbed

section Alg

variable {A k : Type} [CommRing A] [Field k] {m : Type} [Fintype m] [DecidableEq m]

theorem cT_add' (c : A →+* A) (X Y : Matrix m m A) : Formalism.UG.cT c (X + Y) = Formalism.UG.cT c X + Formalism.UG.cT c Y := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_smul' (c : A →+* A) (a : A) (X : Matrix m m A) : Formalism.UG.cT c (a • X) = c a • Formalism.UG.cT c X := by
  ext i j; simp [Formalism.UG.cT]

theorem smul_mul_smul' (a b : A) (P Q : Matrix m m A) : (a • P) * (b • Q) = (a * b) • (P * Q) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem blk_mul (e f u : A) (hef : e * f = 0) (hue : u * e = 0) (huf : u * f = 0) (huu : u * u = u)
    {X1 Y1 X2 Y2 M : Matrix m m A} (h1 : e • X1 = X1) (h2 : f • Y1 = Y1) (h3 : e • X2 = X2) (h4 : f • Y2 = Y2) :
    (X1 + Y1 + u • M) * (X2 + Y2 + u • 1) = X1 * X2 + Y1 * Y2 + u • M := by
  have hfe : f * e = 0 := by rw [mul_comm, hef]
  have a1 : X1 * Y2 = 0 := by rw [← h1, ← h4, smul_mul_smul', hef, zero_smul]
  have a2 : X1 * (u • 1) = 0 := by rw [← h1, Matrix.mul_smul, Matrix.mul_one, smul_smul, hue, zero_smul]
  have a3 : Y1 * X2 = 0 := by rw [← h2, ← h3, smul_mul_smul', hfe, zero_smul]
  have a4 : Y1 * (u • 1) = 0 := by rw [← h2, Matrix.mul_smul, Matrix.mul_one, smul_smul, huf, zero_smul]
  have a5 : (u • M) * X2 = 0 := by rw [← h3, smul_mul_smul', hue, zero_smul]
  have a6 : (u • M) * Y2 = 0 := by rw [← h4, smul_mul_smul', huf, zero_smul]
  have a7 : (u • M) * (u • 1) = u • M := by rw [smul_mul_smul', huu, Matrix.mul_one]
  simp only [add_mul, mul_add, a1, a2, a3, a4, a5, a6, a7, add_zero, zero_add]

variable (c : A →+* A) (e : A) (pr : A →+* k) (sec : k →+ A)

theorem sec_eq (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) (a : k) : e * sec a = sec a := by
  rw [← sec_pr, pr_sec]

theorem sec_mul (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) (a b : k) :
    sec (a * b) = sec a * sec b := by
  calc sec (a * b) = sec (pr (sec a * sec b)) := by rw [map_mul pr, pr_sec, pr_sec]
    _ = e * (sec a * sec b) := sec_pr _
    _ = sec a * sec b := by rw [← mul_assoc, sec_eq e pr sec pr_sec sec_pr]

theorem secM_mul (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) (Z W : Matrix m m k) :
    (Z * W).map sec = Z.map sec * W.map sec := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, sec_mul e pr sec pr_sec sec_pr]

theorem secM_one (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) :
    (1 : Matrix m m k).map sec = e • (1 : Matrix m m A) := by
  have h1 : sec 1 = e := by rw [← map_one pr, sec_pr, mul_one]
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.one_apply, h1]
  · simp [Matrix.one_apply, h]

theorem secM_supp (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) (Z : Matrix m m k) :
    e • Z.map sec = Z.map sec := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, sec_eq e pr sec pr_sec sec_pr]

end Alg

end GlobalTheory.GlEmbed

namespace GlobalTheory.GlEmbed

section Phi

variable {A k : Type} [CommRing A] [Field k] {m : Type} [Fintype m] [DecidableEq m]
variable (c : A →+* A) (e : A) (pr : A →+* k) (sec : k →+ A) (J Ji : Matrix m m A)

def phi (G Gi : Matrix m m k) : Matrix m m A :=
  G.map sec + Formalism.UG.cT c (J * Gi.map sec * Ji) + (1 - e - c e) • (1 : Matrix m m A)

theorem cT_cT' (hcc : ∀ x, c (c x) = x) (X : Matrix m m A) : Formalism.UG.cT c (Formalism.UG.cT c X) = X := by
  ext i j; simp [Formalism.UG.cT, hcc]

theorem cT_three (hh : Formalism.UG.cT c J = J) (P Q : Matrix m m A) :
    Formalism.UG.cT c P * J * Formalism.UG.cT c Q = Formalism.UG.cT c (Q * J * P) := by
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hh, Matrix.mul_assoc]

variable (he : e * e = e) (hef : e * c e = 0) (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x)
include he hef pr_sec sec_pr

theorem hQ (G : Matrix m m k) : e • (J * G.map sec * Ji) = J * G.map sec * Ji := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, secM_supp e pr sec pr_sec sec_pr]

theorem hY (G : Matrix m m k) : c e • Formalism.UG.cT c (J * G.map sec * Ji) = Formalism.UG.cT c (J * G.map sec * Ji) := by
  rw [← cT_smul', hQ c e pr sec J Ji he hef pr_sec sec_pr]

theorem scal : c e * c e = c e ∧ (1 - e - c e) * e = 0 ∧ (1 - e - c e) * c e = 0 ∧
    (1 - e - c e) * (1 - e - c e) = 1 - e - c e := by
  have hff : c e * c e = c e := by rw [← map_mul, he]
  have hue : (1 - e - c e) * e = 0 := by rw [sub_mul, sub_mul, one_mul, he, mul_comm (c e) e, hef]; ring
  have huf : (1 - e - c e) * c e = 0 := by rw [sub_mul, sub_mul, one_mul, hef, hff]; ring
  refine ⟨hff, hue, huf, ?_⟩
  calc (1 - e - c e) * (1 - e - c e) = (1 - e - c e) - (1 - e - c e) * e - (1 - e - c e) * c e := by ring
    _ = 1 - e - c e := by rw [hue, huf]; ring

theorem phi_mul (hJ : Ji * J = 1) (G Gi G' Gi' : Matrix m m k) :
    phi c e sec J Ji G Gi * phi c e sec J Ji G' Gi' = phi c e sec J Ji (G * G') (Gi' * Gi) := by
  obtain ⟨-, hue, huf, huu⟩ := scal c e pr sec he hef pr_sec sec_pr
  unfold phi
  rw [blk_mul e (c e) _ hef hue huf huu (secM_supp e pr sec pr_sec sec_pr G) (hY c e pr sec J Ji he hef pr_sec sec_pr Gi)
    (secM_supp e pr sec pr_sec sec_pr G') (hY c e pr sec J Ji he hef pr_sec sec_pr Gi'),
    secM_mul e pr sec pr_sec sec_pr G G', secM_mul e pr sec pr_sec sec_pr Gi' Gi, ← Formalism.UG.cT_mul]
  congr 3
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Ji J, hJ, Matrix.one_mul]

theorem phi_one (hJ : Ji * J = 1) : phi c e sec J Ji 1 1 = 1 := by
  have hJ' : J * Ji = 1 := mul_eq_one_comm.1 hJ
  unfold phi
  rw [secM_one e pr sec pr_sec sec_pr, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hJ', cT_smul', Formalism.UG.cT_one,
    ← add_smul, ← add_smul]
  have : e + c e + (1 - e - c e) = 1 := by ring
  rw [this, one_smul]

theorem phi_unitary (hcc : ∀ x, c (c x) = x) (hJ : Ji * J = 1) (hh : Formalism.UG.cT c J = J) (G Gi : Matrix m m k)
    (hG : Gi * G = 1) :
    Formalism.UG.cT c (phi c e sec J Ji G Gi) * J * phi c e sec J Ji G Gi = J := by
  obtain ⟨-, hue, huf, huu⟩ := scal c e pr sec he hef pr_sec sec_pr
  have hcu : c (1 - e - c e) = 1 - e - c e := by rw [map_sub, map_sub, map_one, hcc]; ring
  set S := G.map sec with hSdef
  set Q := J * Gi.map sec * Ji with hQdef
  have hS : e • S = S := secM_supp e pr sec pr_sec sec_pr G
  have hQ' : e • Q = Q := hQ c e pr sec J Ji he hef pr_sec sec_pr Gi
  have hL : c e • Formalism.UG.cT c S = Formalism.UG.cT c S := by rw [← cT_smul', hS]
  have h1 : Formalism.UG.cT c (phi c e sec J Ji G Gi) * J = Q * J + Formalism.UG.cT c S * J + (1 - e - c e) • J := by
    unfold phi
    rw [← hSdef, ← hQdef, cT_add', cT_add', cT_smul', Formalism.UG.cT_one, cT_cT' c hcc, hcu]
    simp only [add_mul, Matrix.smul_mul, Matrix.one_mul]
    abel
  have hQJ : e • (Q * J) = Q * J := by rw [← Matrix.smul_mul, hQ']
  have hLJ : c e • (Formalism.UG.cT c S * J) = Formalism.UG.cT c S * J := by rw [← Matrix.smul_mul, hL]
  rw [h1]
  unfold phi
  rw [← hSdef, ← hQdef, blk_mul e (c e) _ hef hue huf huu hQJ hLJ hS (hY c e pr sec J Ji he hef pr_sec sec_pr Gi)]
  have h2 : Q * J * S = e • J := by
    rw [hQdef, hSdef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ji J, hJ, Matrix.one_mul, ← secM_mul e pr sec pr_sec sec_pr, hG,
      secM_one e pr sec pr_sec sec_pr, Matrix.mul_smul, Matrix.mul_one]
  have h3 : Formalism.UG.cT c S * J * Formalism.UG.cT c Q = c e • J := by
    rw [cT_three c J hh, h2, cT_smul', hh]
  rw [h2, h3, ← add_smul, ← add_smul]
  have : e + c e + (1 - e - c e) = 1 := by ring
  rw [this, one_smul]

theorem phi_map (G Gi : Matrix m m k) : (phi c e sec J Ji G Gi).map pr = G := by
  obtain ⟨-, hue, huf, huu⟩ := scal c e pr sec he hef pr_sec sec_pr
  have hpe : pr e = 1 := by
    have h1 : sec 1 = e := by rw [← map_one pr, sec_pr, mul_one]
    rw [← h1, pr_sec]
  have hpf : pr (c e) = 0 := by
    have := congrArg pr hef
    rwa [map_mul, map_zero, hpe, one_mul] at this
  have hpu : pr (1 - e - c e) = 0 := by rw [map_sub, map_sub, map_one, hpe, hpf]; ring
  have hYe := hY c e pr sec J Ji he hef pr_sec sec_pr Gi
  ext i j
  have hij : Formalism.UG.cT c (J * Gi.map sec * Ji) i j = c e * Formalism.UG.cT c (J * Gi.map sec * Ji) i j := by
    conv_lhs => rw [← hYe]
    rfl
  unfold phi
  rw [Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, map_add (f := _), map_add (f := _), hij, Matrix.smul_apply, smul_eq_mul,
    map_mul, map_mul, hpf, hpu, Matrix.map_apply, pr_sec]
  ring

theorem phi_supp (G Gi : Matrix m m k) :
    (e + c e) • (phi c e sec J Ji G Gi - 1) = phi c e sec J Ji G Gi - 1 := by
  obtain ⟨hff, -, -, -⟩ := scal c e pr sec he hef pr_sec sec_pr
  have hS := secM_supp e pr sec pr_sec sec_pr G
  have hYe := hY c e pr sec J Ji he hef pr_sec sec_pr Gi
  ext i j
  have hs : e * G.map sec i j = G.map sec i j := by
    conv_rhs => rw [← hS]
    rfl
  have hy : c e * Formalism.UG.cT c (J * Gi.map sec * Ji) i j = Formalism.UG.cT c (J * Gi.map sec * Ji) i j := by
    conv_rhs => rw [← hYe]
    rfl
  unfold phi
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  linear_combination (1 - c e) * hs + (1 - e) * hy +
    (G.map sec i j + Formalism.UG.cT c (J * Gi.map sec * Ji) i j - 2 * (1 : Matrix m m A) i j) * hef -
    (1 : Matrix m m A) i j * he - (1 : Matrix m m A) i j * hff

end Phi

end GlobalTheory.GlEmbed

namespace GlobalTheory.GlEmbed

variable {D : D7}

theorem cT_JR (S : HSp D) : Formalism.UG.cT (cA D) (S.gram.map (incA D)) = S.gram.map (incA D) := by
  ext i j
  have hh : D.sp.cm.sig (S.gram j i) = S.gram i j := S.herm.eq (S.frame j) (S.frame i)
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [← hh]
  simp [cA, sigR, inclR, incA]

theorem JR_inv_mul (S : HSp D) (h : IsUnit S.gram.det) :
    (S.gram⁻¹).map (incA D) * S.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_gl (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (b : Matrix (Fin S.rank) n k)
    (b' : Matrix n (Fin S.rank) k) : b * b' = 1 → b' * b = 1 →
    ∃ gl : GL n k →* GA D S, (∀ g, SuppAt p.e S (gl g)) ∧ ∀ g, (mt S (gl g)).map p.pr = b * g.val * b' := by
  intro bb' b'b
  obtain ⟨he, hef, -⟩ := p.split
  set J := S.gram.map (incA D) with hJdef
  set Ji := (S.gram⁻¹).map (incA D) with hJidef
  have hJ : Ji * J = 1 := JR_inv_mul S (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit S)
  have hh : Formalism.UG.cT (cA D) J = J := cT_JR S
  have hcc : ∀ x, cA D (cA D x) = x := Formalism.L2.Theta.cA_cA
  have Gmul : ∀ g h : Matrix n n k, b * g * b' * (b * h * b') = b * (g * h) * b' := fun g h => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b' b, b'b, Matrix.one_mul]
  let Φ : GL n k →* Matrix (Fin S.rank) (Fin S.rank) (AE D) :=
    { toFun := fun g => phi (cA D) p.e p.sec J Ji (b * g.val * b') (b * (g⁻¹).val * b')
      map_one' := by
        simp only [inv_one, Units.val_one, Matrix.mul_one, bb']
        exact phi_one (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr hJ
      map_mul' := fun g h => by
        rw [phi_mul (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr hJ, Gmul, Gmul, mul_inv_rev, Units.val_mul,
          Units.val_mul] }
  have hmem : ∀ g, Φ.toHomUnits g ∈ HR (AF D.host.F) D.sp.cm.sig S.gram := fun g => by
    show Formalism.UG.cT (cA D) (Φ g) * J * Φ g = J
    refine phi_unitary (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr hcc hJ hh _ _ ?_
    rw [Gmul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, bb']
  refine ⟨Φ.toHomUnits.codRestrict _ hmem, fun g => ?_, fun g => ?_⟩
  · intro i j
    have h := phi_supp (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr (b * g.val * b') (b * (g⁻¹).val * b')
    exact congrFun (congrFun h i) j
  · exact phi_map (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr _ _

end GlobalTheory.GlEmbed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.FinPl
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

def intV (D : D7) (v : Pl D) : AddSubgroup (Fv D.host.F v ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {y | ∃ a ∈ v.adicCompletionIntegers D.host.F, ∃ x : 𝓞 D.host.E, y = a ⊗ₜ[D.host.F] (x : D.host.E)}

def sigV (D : D7) (v : Pl D) : Fv D.host.F v ⊗[D.host.F] D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E :=
  Algebra.TensorProduct.map (AlgHom.id D.host.F (Fv D.host.F v)) D.sp.cm.sig

end GlobalTheory.FixedUnitNorm

end
end

