module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumBLieMemHtLatIffOfPointOver
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
open GlobalTheory.KernelNoTorsion
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.IndepPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P P' : Point p v O Λ}

def ptsHom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (T : Over S) :
    (T ⟶ A) →* (T ⟶ B) :=
  MonoidHom.mk' (fun x => x ≫ f) fun x y => MonObj.mul_comp x y _


variable [IsAlgClosed C] [CharZero C]

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]


variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (e : P.T ≃ₗ[ℤ_[p]] P'.T)




end GlobalTheory.CompHt.IndepPoint

namespace GlobalTheory.CompHt

open IndepPoint

end GlobalTheory.CompHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgePrimitiveOneFormsEqZeroAbelianScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

private lemma add_add_eq_add_imp {M : Type} [AddCommGroup M] (a b c d : M) (h : (a + b) + (c + d) = a + d) :
    c + b = 0 := by
  calc c + b = (a + b) + (c + d) - (a + d) := by abel
    _ = 0 := by rw [h, sub_self]

theorem wsum_eq_zero_of_mul : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (n : ℕ) (u v : Fin n → GlobForm A.hom), wsum (OAff (A ⊗ A).hom) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (v k)) = wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (fst A A) (v k)) + wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (snd A A) (u k)) (fun k ↦ pF (snd A A) (v k)) → wsum (OAff A.hom) u v = 0 := by
  intro R _ A _ g hA hs n u v hw
  have hP : ∀ x : GlobForm A.hom, pF μ[A] x = pF (fst A A) x + pF (snd A A) x := GlobalTheory.T.abelianScheme_globalOneForms_primitive R A g hA hs
  obtain ⟨hF, hC, hA2, hs2⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hs
  obtain ⟨hF2, hC2, -, -⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R (A ⊗ A) (g + g) hA2 hs2
  obtain ⟨-, hax, -⟩ := _root_.GlobalTheory.AbCoh.AxesPull.main R A
  let U : Fin (n + n) → GlobForm (A ⊗ A).hom :=
    Fin.append (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (snd A A) (u k))
  let V : Fin (n + n) → GlobForm (A ⊗ A).hom :=
    Fin.append (fun k ↦ pF (snd A A) (v k)) (fun k ↦ pF (fst A A) (v k))
  have hUV : wsum (OAff (A ⊗ A).hom) U V = 0 := by
    funext T
    have h1 := congrFun hw T
    simp only [wsum, hP, Submodule.coe_add, Pi.add_apply, map_add (f := _), LinearMap.add_apply,
      Finset.sum_add_distrib] at h1
    simp only [wsum, Fin.sum_univ_add, U, V, Fin.append_left, Fin.append_right]
    exact add_add_eq_add_imp _ _ _ _ h1
  have key := (_root_.GlobalTheory.AbCoh.wsum_eq_zero_iff R _ (OAff (A ⊗ A).hom) hF2 hC2 (n + n) U V).mp hUV
  refine (_root_.GlobalTheory.AbCoh.wsum_eq_zero_iff R _ (OAff A.hom) hF hC n u v).mpr ?_
  intro l l'
  have h2 := key (l ∘ₗ pF (lift (𝟙 A) (toUnit A ≫ η[A]))) (l' ∘ₗ pF (lift (toUnit A ≫ η[A]) (𝟙 A)))
  simp only [Fin.sum_univ_add, U, V, Fin.append_left, Fin.append_right, LinearMap.comp_apply,
    (hax _).1, (hax _).2.1, (hax _).2.2.2.1, (hax _).2.2.2.2.1, map_zero, mul_zero, zero_mul, sub_zero,
    zero_sub] at h2
  rw [← h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymPrOpenBounded
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.SymImageC

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def refLev (p : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * p + 1) (fun i => 2 * (i.val + 1))

def refGroup (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | GlobalTheory.RootEx.Radical.Uni (refLev p) g.val}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun ha hb => GlobalTheory.RootEx.Radical.Uni.mul ha hb
  inv_mem' := fun ha => GlobalTheory.RootEx.Radical.Uni.inv ha

theorem N_le_refGroup {p q : ℕ} (h₁ : p ≤ q) (h₂ : q ≤ p + 1) :
    GlobalTheory.RootEx.N k n c q ≤ refGroup k n c p := by
  intro g hg r s hrs
  refine (GlobalTheory.RootEx.Radical.mem_N_iff g).1 hg r s ?_
  rcases r with r | r <;> rcases s with s | s <;>
    simp only [refLev, Sum.elim_inl, Sum.elim_inr] at hrs <;>
    simp only [GlobalTheory.RootEx.lev, Sum.elim_inl, Sum.elim_inr] <;> omega

theorem symN_le_refGroup : symN k n c ≤ refGroup k n c ((c + 1) / 2) :=
  sup_le (N_le_refGroup le_rfl (by omega)) (N_le_refGroup (by omega) (by omega))

theorem toBlocks₁₁_of_mem_symN {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) : u.val.toBlocks₁₁ = 1 := by
  have h : GlobalTheory.RootEx.Radical.Uni (refLev ((c + 1) / 2)) u.val := symN_le_refGroup hu
  ext r s
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
  rw [h _ _ (by simp [refLev])]
  simp [Matrix.one_apply]

theorem toBlocks₁₁_mul_embX {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) (g : GL n k) :
    (u * GlobalTheory.RootEx.embX c g).val.toBlocks₁₁ = g.val := by
  have h := toBlocks₁₁_of_mem_symN hu
  rw [Units.val_mul, GlobalTheory.RootEx.Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks u.val]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, h]
  simp

theorem toBlocks₁₁_inv_mul_embX {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) (g : GL n k) :
    ((u * GlobalTheory.RootEx.embX c g)⁻¹).val.toBlocks₁₁ = (g⁻¹).val := by
  have h := toBlocks₁₁_of_mem_symN (inv_mem hu)
  rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul, GlobalTheory.RootEx.Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (u⁻¹).val]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, h]
  simp

end GlobalTheory.FunObj.SymImageC


open GlobalTheory.FunObj.SymImageC in
theorem GlobalTheory.FunObj.SymImageC.symPr_open_bounded {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (C : Subgroup (GL (n ⊕ Fin c) k)) (hC : IsOpen (C : Set (GL (n ⊕ Fin c) k)))
    (hb : ∃ A : Set (GL (n ⊕ Fin c) k), IsCompact A ∧ (C : Set (GL (n ⊕ Fin c) k)) ⊆ A) :
    IsOpen (symPr C : Set (GL n k)) ∧ ∃ A : Set (GL n k), IsCompact A ∧ (symPr C : Set (GL n k)) ⊆ A := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  constructor
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    have ho := hC.preimage (GlobalTheory.RootEx.QuotLinear.continuous_embX (k := k) (n := n) (c := c))
    refine Filter.mem_of_superset (ho.mem_nhds (by simp [one_mem])) fun g hg => ?_
    exact ⟨1, one_mem _, by simpa using hg⟩
  · obtain ⟨A, hA, hCA⟩ := hb
    let φ : GL (n ⊕ Fin c) k → Matrix n n k × (Matrix n n k)ᵐᵒᵖ :=
      fun g => (g.val.toBlocks₁₁, MulOpposite.op (g⁻¹).val.toBlocks₁₁)
    have hbl : Continuous fun M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => M.toBlocks₁₁ :=
      continuous_matrix fun i j => continuous_id.matrix_elem _ _
    have hφ : Continuous φ :=
      (hbl.comp Units.continuous_val).prodMk
        (MulOpposite.continuous_op.comp (hbl.comp Units.continuous_coe_inv))
    refine ⟨_, (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (hA.image hφ),
      ?_⟩
    rintro g ⟨u, hu, h⟩
    refine ⟨_, hCA h, ?_⟩
    simp only [φ]
    rw [toBlocks₁₁_mul_embX hu, toBlocks₁₁_inv_mul_embX hu]
    rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNZOfPolAt
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ThetaNormal

theorem thetaNZ_of_polAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.admitted R (IsLocalRing.maximalIdeal R) → ∀ (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → GlobalTheory.LN.SplitOver t.G (IsLocalRing.maximalIdeal R) → GlobalTheory.LN.ThetaNZ t.G t.PP.L := by
  intro E _ _ _ H R _ _ _ hA t hpol hs
  obtain ⟨h1, h2, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨A, -, gen, hgen, hL, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt h1 h2 E H R t hpol
  have := hA.1.1
  obtain ⟨P, hPL, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric h1 R A t.G t.semi gen hgen t.PP t.cub t.sym
  have hσ : ∃ (σ : LB.Sec P.L.L) (k : P.L.L.ι), σ.f k ≠ 0 := by
    rw [hPL]; exact _root_.GlobalTheory.ThetaDomain.exists_sec_ne_zero_of_polAt E H R t hpol
  obtain ⟨D, U, hUL, -⟩ := _root_.GlobalTheory.SectionUnif.exists_unif_of_ne_zero R hA t.G P t.semi (hPL ▸ GlobalTheory.LN.UnifPrime.hypW_of_triple t) hs A gen hgen
    (hPL ▸ hL) hσ
  have key := _root_.GlobalTheory.ThetaClosed.exists_section_nonzero_closed R hA.1.1 hA.1.2.2.1 hA.2.1 hA.2.2.1 D A t.G t.semi U
  rw [hUL, hPL] at key
  have := t.semi.smooth
  exact GlobalTheory.UnifNormal.thetaNZ_of_closedPoint t.G _ key

end GlobalTheory.ThetaNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeAndExistsRatPtsSwap
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResLine.Swap

section Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem cT_add' (σ : E →ₐ[F] E) {a b : Type} (M N : Matrix a b E) :
    Formalism.UG.cT (σ : E →+* E) (M + N) = Formalism.UG.cT (σ : E →+* E) M + Formalism.UG.cT (σ : E →+* E) N := by
  ext i j; simp [Formalism.UG.cT]

omit [NumberField F] [NumberField E] in
theorem cT_sub' (σ : E →ₐ[F] E) {a b : Type} (M N : Matrix a b E) :
    Formalism.UG.cT (σ : E →+* E) (M - N) = Formalism.UG.cT (σ : E →+* E) M - Formalism.UG.cT (σ : E →+* E) N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_cT_of_isCMExt {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {a b : Type} (M : Matrix a b E) :
    Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) M) = M := by
  ext i j; simp [Formalism.UG.cT, GlobalTheory.SiegelSet.sigma_sigma hσ]

omit [NumberField F] [NumberField E] in
theorem cT_eq_of_isHermND {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) :
    Formalism.UG.cT (σ : E →+* E) J = J := by
  ext i j; simpa [Formalism.UG.cT] using hJ.1 i j

end Swap

end GlobalTheory.ResLine.Swap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingCharacterPhaseOriginValuationLeBox
section
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.OriginBox

section Entries
variable {k : Type} [Field k] {n n' : Type} {c : ℕ}

theorem stepPt_var (x₀ : Matrix n n' k) (e : StepVar n c n' → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) (hb : basePt c x₀ r s = 0) : stepPt x₀ e r s = e ⟨(r, s), h⟩ := by
  simp only [stepPt, Matrix.add_apply, Matrix.of_apply, hb, zero_add, dif_pos h]

theorem basePt_inr_succ (x₀ : Matrix n n' k) (i : Fin c) : basePt c x₀ (.inr i) (.inr i.succ) = 0 := by
  simp [basePt]

theorem basePt_inl_inr (x₀ : Matrix n n' k) (r : n) (i : Fin (c + 1)) : basePt c x₀ (.inl r) (.inr i) = 0 := by
  simp [basePt]

theorem basePt_inr_inl (x₀ : Matrix n n' k) (l : Fin c) (s : n') : basePt c x₀ (.inr l) (.inl s) = 0 := by
  simp [basePt]

end Entries

section Main
variable {k : Type} [Field k] [ValuativeRel k]

theorem phase_origin_le (G : Grid k) (ϖ : kˣ) (a a' : ℤ) (e : Vars G) (he : e ∈ box G ϖ a a') :
    valuation k (phase (0 : ColArgs G) e) ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) := by
  have hbox : ∀ j v {A : ℤ}, boxExp G a a' j v = A → valuation k (e j v) ≤ valuation k ((ϖ ^ A : kˣ) : k) :=
    fun j v A hA => hA ▸ he j (Set.mem_univ j) v (Set.mem_univ v)
  have hmul : ∀ {x y : k} {A B : ℤ}, valuation k x ≤ valuation k ((ϖ ^ A : kˣ) : k) →
      valuation k y ≤ valuation k ((ϖ ^ B : kˣ) : k) → A + B = a + a' →
      valuation k (x * y) ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) := by
    intro x y A B hx hy hAB
    rw [← hAB, _root_.zpow_add, Units.val_mul, map_mul, map_mul]
    exact mul_le_mul' hx hy
  unfold phase
  refine Valuation.map_sum_le _ fun j _ => Valuation.map_add_le _ ?_ ?_
  · unfold ch
    refine Valuation.map_sum_le _ fun i _ => ?_
    rw [stepPt_var _ _ (Or.inl (by simp [Free])) (basePt_inr_succ _ i)]
    refine hbox _ _ ?_
    simp only [boxExp, auxiliaryVectorUniformizerExponent, Fin.val_succ]
    push_cast
    ring
  · split_ifs with hc
    · refine Valuation.map_sum_le _ fun r _ => ?_
      unfold rowVar
      split_ifs with h
      · rw [Finset.sum_mul]
        refine Valuation.map_sum_le _ fun l _ => ?_
        split_ifs with hl
        · have hc' : Odd (G.m - 2 - (j + 1)) := by
            obtain ⟨q, hq⟩ := hc
            exact ⟨q - 1, by omega⟩
          unfold colVar
          rw [stepPt_var (c := G.m - 2 - (j + 1)) (r := .inr l) (s := .inl r) _ _ (Or.inr ⟨hc', hl⟩) (basePt_inr_inl _ l r),
            stepPt_var (c := G.m - 2 - j) (r := .inl r) (s := .inr ⟨(G.m - 2 - j) / 2, by omega⟩) _ _ (Or.inr ⟨hc, rfl⟩) (basePt_inl_inr _ r _)]
          refine hmul (hbox _ _ rfl) (hbox _ _ rfl) ?_
          obtain ⟨q, hq⟩ := hc
          have h1 : (G.m - 2 - (j + 1) : ℕ) = q + q - 1 := by omega
          have h2 : (l : ℕ) + 1 = q := by omega
          have h3 : (G.m - 2 - j) / 2 = q := by omega
          have h4 : (((q + q - 1 : ℕ)) : ℤ) = 2 * (q : ℤ) - 1 := by omega
          have h5 : ((l : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
          simp only [boxExp, auxiliaryVectorUniformizerExponent]
          rw [h5, h3, hq, h1, h4]
          push_cast
          ring
        · simp
      · simp
    · simp

end Main
end GlobalTheory.OriginBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerOfValuationRingFixedFieldInertia
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaFixedUniformizer

theorem valuation_uniformizer_lt_one {R K Ω : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring)
    {π : R} (hπ : Irreducible π) : V.valuation (algebraMap K Ω (algebraMap R K π)) < 1 := by
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hle : V.valuation (algebraMap K Ω (algebraMap R K π)) ≤ 1 := by
    rw [V.valuation_le_one_iff]
    have : algebraMap R K π ∈ (V.toSubring).comap (algebraMap K Ω) := by
      rw [hV]; exact ⟨π, rfl⟩
    exact this
  refine lt_of_le_of_ne hle fun h1 => hπ.not_isUnit ?_
  have hinv : (algebraMap R K π)⁻¹ ∈ (V.toSubring).comap (algebraMap K Ω) := by
    change algebraMap K Ω (algebraMap R K π)⁻¹ ∈ V
    rw [← V.valuation_le_one_iff, map_inv₀, map_inv₀, h1, inv_one]
  rw [hV] at hinv
  obtain ⟨u, hu⟩ := hinv
  refine IsUnit.of_mul_eq_one u (IsFractionRing.injective R K ?_)
  rw [map_mul, hu, mul_inv_cancel₀ hπ0, map_one]

theorem uniformizer_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π →
    V.valuation (algebraMap K Ω (algebraMap R K π)) < 1 ∧
      ∀ y : IntermediateField.fixedField (inertia K V), V.valuation (y : Ω) < 1 →
        ∃ z : IntermediateField.fixedField (inertia K V), (z : Ω) ∈ V ∧
          y = algebraMap K _ (algebraMap R K π) * z := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV π hπ
  refine ⟨valuation_uniformizer_lt_one V hV hπ, fun y hy => ?_⟩
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hmem := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (y : Ω) y.2
    ((ValuationSubring.mem_nonunits_iff _).2 hy)
  refine ⟨y / algebraMap K _ (algebraMap R K π), ?_, ?_⟩
  · simpa using hmem
  · rw [mul_div_cancel₀]
    exact (map_ne_zero _).2 hπ0

end GlobalTheory.InertiaFixedUniformizer
end

