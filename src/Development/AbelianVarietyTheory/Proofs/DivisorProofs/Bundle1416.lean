module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0733
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1381
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalHarishChandraFiniteFormBoundedDetNormBan
section
namespace GlobalTheory.HCF

open NumberField MeasureTheory GlobalTheory.CuspRep Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

theorem bounded_on_band_of_cuspidal : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∃ M : ℝ, ∀ g ∈ band E a, ‖φ.1 g‖ ≤ M := by
  intro E _ _ _ a L hL W hW X hX N φ hφ hcusp
  have hleft : ∀ ψ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ γ g, ψ.1 (ratGL E a γ * g) = ψ.1 g := by
    intro ψ hψ γ g
    induction hψ using Submodule.span_induction with
    | mem x hx => exact hx.1.left γ g
    | zero => rfl
    | add x y _ _ hx hy =>
      change x.1 (ratGL E a γ * g) + y.1 (ratGL E a γ * g) = x.1 g + y.1 g
      rw [hx, hy]
    | smul c x _ hx =>
      change c * x.1 (ratGL E a γ * g) = c * x.1 g
      rw [hx]
  obtain ⟨Ω, hΩc, hΩB, t, c₁, c₂, ht, hc₁, hred⟩ := GlobalTheory.T.exists_siegelSet_reduction_adelicDetNormBand E a
  obtain ⟨C₀, N₀, hC₀, hpoly⟩ := GlobalTheory.T.moderateGrowth_span_harishChandraFiniteForms E a L hL W X N φ hφ Ω hΩc
  obtain ⟨β, hβ, hβc, hβs, hrep⟩ := _root_.GlobalTheory.HCSmoothGL.exists_smooth_beta E a L W hW X hX N
  obtain ⟨C', K, hC', hineq⟩ := _root_.GlobalTheory.RatioIneq.sum_add_inv_le_of_ratio_bounds a t c₁ c₂ ht hc₁
  obtain ⟨Cm, hCm, hdec⟩ := GlobalTheory.T.cuspidal_rapidDecay_one_simpleRoot E a L hL W X N β hβ hβc hβs hrep φ hφ hcusp Ω hΩc hΩB t C₀ N₀ ht hpoly (K * N₀)
  refine ⟨max (C₀ * C' ^ N₀ * height (1 : GL (Fin a) (Cinf E)) ^ N₀) (Cm * C' ^ N₀), fun g hg => ?_⟩
  obtain ⟨γ, b, hb, r, hr, hrat, hp1, hp2, k, hk, hg'⟩ := hred g hg
  rw [← hleft φ hφ γ g, hg']
  have hs0 : 0 ≤ ∑ i, (r i + (r i)⁻¹) := Finset.sum_nonneg fun i _ => by have := hr i; positivity
  by_cases hP : ∃ i j : Fin a, (j : ℕ) = i + 1 ∧ 1 ≤ r i / r j
  · obtain ⟨i₀, j₀, hij₀, h1⟩ := hP
    obtain ⟨p, hpP, hpmax⟩ := ((Finset.univ : Finset (Fin a × Fin a)).filter
      (fun p => (p.2 : ℕ) = p.1 + 1)).exists_max_image (fun p => r p.1 / r p.2)
      ⟨(i₀, j₀), by simp [hij₀]⟩
    have hpP' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.1 hpP).2
    have hρ1 : 1 ≤ r p.1 / r p.2 := le_trans h1 (hpmax (i₀, j₀) (by simp [hij₀]))
    have hρ0 : 0 < r p.1 / r p.2 := by linarith
    have hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ (r p.1 / r p.2) * r j := fun i j hij => by
      have := hpmax (i, j) (by simp [hij])
      rwa [div_le_iff₀ (hr j)] at this
    have hsle := hineq r hr hrat hp1 hp2 _ hρ1 hall
    have hd := hdec b hb r hr hrat k hk p.1 p.2 hpP'
    refine le_trans hd (le_trans ?_ (le_max_right _ _))
    have e : r p.2 / r p.1 = (r p.1 / r p.2)⁻¹ := by rw [inv_div]
    rw [e]
    calc Cm * (r p.1 / r p.2)⁻¹ ^ (K * N₀) * (∑ i, (r i + (r i)⁻¹)) ^ N₀
        ≤ Cm * (r p.1 / r p.2)⁻¹ ^ (K * N₀) * (C' * (r p.1 / r p.2) ^ K) ^ N₀ := by
          gcongr
      _ = Cm * C' ^ N₀ := by
          rw [mul_pow, ← pow_mul, inv_pow]
          field_simp
  · push_neg at hP
    have hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ 1 * r j := fun i j hij => by
      have := (hP i j hij).le
      rwa [div_le_iff₀ (hr j)] at this
    have hsle := hineq r hr hrat hp1 hp2 1 le_rfl hall
    rw [one_pow, mul_one] at hsle
    have hb' := hpoly b hb r hr k hk 1
    rw [map_one, mul_one] at hb'
    refine le_trans hb' (le_trans ?_ (le_max_left _ _))
    have hh : 0 ≤ height (1 : GL (Fin a) (Cinf E)) := le_trans zero_le_one (one_le_height _)
    gcongr

end GlobalTheory.HCF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

variable {n : ℕ}

def dOne (f : V n → ℂ) (v : V n) : Alt n := ∑ a, del f v (coordVec a) • dz a

theorem delAt_eq_sum_dOne (β : V n → Alt n) (u : V n) :
    delAt β u = ∑ T, dOne (fun x => (bas n).repr (β x) T) u * bas n T := by
  simp only [delAt, coefwise, dOne, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  exact Finset.sum_comm

theorem delAt_congr {F G : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] G) : delAt F v = delAt G v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => congrArg _ (Finset.sum_congr rfl fun S _ => ?_)
  have e : del (fun x => (bas n).repr (F x) S) v = del (fun x => (bas n).repr (G x) S) v :=
    del_congr (h.fun_comp fun y => (bas n).repr y S)
  simp only [e]

end GlobalTheory.CxForm.DelForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTracePowGramNeZero
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceGram

theorem det_trace_pow_gram_ne_zero {K : Type} [Field K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : g.charpoly.Separable) :
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 := by
  set L := AlgebraicClosure K
  set f : K →+* L := algebraMap K L
  set M : Matrix (Fin n) (Fin n) L := g.map f
  have hMc : M.charpoly = g.charpoly.map f := Matrix.charpoly_map g f
  have hnd : M.charpoly.roots.Nodup := by
    rw [hMc]; exact nodup_roots (hg.map)
  have hcard : M.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, GlobalTheory.CharpolyPow.card_roots_charpoly]
  set s := M.charpoly.roots.toFinset
  let e : Fin n ≃ s := (Fin.castOrderIso hcard.symm).toEquiv.trans s.equivFin.symm
  let v : Fin n → L := fun i => (e i : L)
  have hv : Function.Injective v := fun a b h => e.injective (Subtype.ext h)
  have hsum : ∀ φ : L → L, (M.charpoly.roots.map φ).sum = ∑ i, φ (v i) := by
    intro φ
    have : M.charpoly.roots = s.val := by
      simp [s, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
    rw [this, ← Finset.sum_eq_multiset_sum, ← Finset.sum_coe_sort s]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  have htr : ∀ m : ℕ, f (g ^ m).trace = ∑ i, v i ^ m := by
    intro m
    have h1 : f (g ^ m).trace = (M ^ m).trace := by
      have hp : M ^ m = (g ^ m).map f := by simp [M, Matrix.map_pow]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hp]; simp [Matrix.trace, Matrix.map_apply, map_sum]
    rw [h1, Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow, hsum]
  have hG : (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).map f
      = (vandermonde v)ᵀ * vandermonde v := by
    ext i j
    rw [vandermonde_transpose_mul_vandermonde, Matrix.map_apply, Matrix.of_apply, htr]
  intro h0
  have hd := RingHom.map_det f (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace)
  rw [h0, map_zero] at hd
  have h2 : ((vandermonde v)ᵀ * vandermonde v).det = 0 := by
    rw [← hG]; exact hd.symm
  rw [det_mul, det_transpose, mul_self_eq_zero] at h2
  exact det_vandermonde_ne_zero_iff.mpr hv h2

end GlobalTheory.TraceGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceSplittingConstantHalfRealPlacesStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledSpace_splitting_constant_half_realPlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)) (χ : Chr F E) (m : InfinitePlace F → ℤ)
    (cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C →
    IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) JA (dbl JB) dd χ (diagCols β) omd → HasExp τ χ m →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x)) →
    (∫ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x)) ≠ 0 →
    0 < R + S → ∀ w, cd w = m w / 2 := by
  first | exact @GlobalTheory.RealLift.DConst.cd_eq_half_exp | exact GlobalTheory.RealLift.DConst.cd_eq_half_exp | (intros; apply GlobalTheory.RealLift.DConst.cd_eq_half_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolyConjSelfReciprocalCoeff
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjSelfRecip

theorem ell_coeff_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    P.coeff 0 ≠ 0 ∧ ∀ k ≤ n, P.coeff 0 * IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) := by
  intro E _ _ _ n P hP
  have hdeg : P.natDegree = n := hP.2.1
  obtain ⟨h0, hid⟩ := ell_conj_selfRecip E n P hP
  refine ⟨h0, fun k hk => ?_⟩
  have hc := congrArg (fun Q : E[X] => Q.coeff k) hid
  simp only [coeff_C_mul, coeff_reverse] at hc
  have hnd : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).natDegree = n := by
    rw [natDegree_map_eq_of_injective (IsCMField.complexConj E).toRingEquiv.toRingHom.injective, hdeg]
  rw [hnd, revAt_le hk, coeff_map] at hc
  have hc2 := congrArg (IsCMField.complexConj E) hc
  simpa [map_mul] using hc2

end GlobalTheory.ConjSelfRecip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderOfTrivialModSqTateModule
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.MinkowskiTate

section Lemmas

variable {l : ℕ} {M : Type} [CommGroup M]

theorem lev_nsmul (t : Tate l M) (n m : ℕ) : (n • t).lev m = t.lev m ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero]; rfl
  | succ n ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

theorem lev_neg (t : Tate l M) (m : ℕ) : (-t).lev m = (t.lev m)⁻¹ := rfl

theorem lev_sub (s t : Tate l M) (m : ℕ) : (s - t).lev m = s.lev m * (t.lev m)⁻¹ := by
  rw [sub_eq_add_neg, Tate.lev_add, lev_neg]

def Dv (k : ℕ) (t : Tate l M) : Prop := ∃ s : Tate l M, t = (l ^ k) • s

theorem dv_zero (k : ℕ) : Dv k (0 : Tate l M) := ⟨0, (smul_zero _).symm⟩

theorem dv_add {k : ℕ} {s t : Tate l M} (hs : Dv k s) (ht : Dv k t) : Dv k (s + t) := by
  obtain ⟨a, rfl⟩ := hs
  obtain ⟨b, rfl⟩ := ht
  exact ⟨a + b, (smul_add _ _ _).symm⟩

theorem dv_neg {k : ℕ} {t : Tate l M} (ht : Dv k t) : Dv k (-t) := by
  obtain ⟨a, rfl⟩ := ht
  exact ⟨-a, (smul_neg _ _).symm⟩

theorem dv_nsmul {k : ℕ} (n : ℕ) {t : Tate l M} (ht : Dv k t) : Dv k (n • t) := by
  obtain ⟨a, rfl⟩ := ht
  exact ⟨n • a, smul_comm _ _ _⟩

theorem dv_sum {k : ℕ} {Ix : Type} (s : Finset Ix) (f : Ix → Tate l M) (h : ∀ i ∈ s, Dv k (f i)) :
    Dv k (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Dv k) (fun _ _ => dv_add) (dv_zero k) h

theorem dv_mono {k k' : ℕ} (hk : k ≤ k') {t : Tate l M} (ht : Dv k' t) : Dv k t := by
  obtain ⟨a, rfl⟩ := ht
  refine ⟨l ^ (k' - k) • a, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hk]

theorem eq_zero_of_nsmul {t : Tate l M} (h : l • t = 0) : t = 0 := by
  refine Tate.ext fun m => ?_
  show t.lev m = 1
  calc t.lev m = t.lev (m + 1) ^ l := (Tate.lev_succ t m).symm
    _ = (l • t).lev (m + 1) := (lev_nsmul t l (m + 1)).symm
    _ = 1 := by rw [h]; rfl

theorem eq_zero_of_pow_nsmul (a : ℕ) {z : Tate l M} (h : (l ^ a) • z = 0) : z = 0 := by
  induction a generalizing z with
  | zero => simpa using h
  | succ a ih => exact eq_zero_of_nsmul (ih (by rw [smul_smul, ← pow_succ]; exact h))

theorem pow_nsmul_cancel (a : ℕ) {x y : Tate l M} (h : (l ^ a) • x = (l ^ a) • y) : x = y :=
  sub_eq_zero.1 (eq_zero_of_pow_nsmul a (by rw [smul_sub, h, sub_self]))

theorem dv_of_pow_nsmul {a b : ℕ} {s : Tate l M} (h : Dv (a + b) ((l ^ a) • s)) : Dv b s := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, pow_nsmul_cancel a (by rw [hr, pow_add, smul_smul])⟩

theorem dv_one_of_nsmul {q : ℕ} (hq : Nat.Coprime q l) {s : Tate l M} (h : Dv 1 (q • s)) :
    Dv 1 s := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hq
  refine ⟨a • r + b • s, ?_⟩
  calc s = (a * (q : ℤ) + b * (l : ℤ)) • s := by rw [hab, one_smul]
    _ = a • ((q : ℤ) • s) + b • ((l : ℤ) • s) := by rw [add_smul, mul_smul, mul_smul]
    _ = l ^ 1 • (a • r + b • s) := by
      rw [natCast_zsmul, natCast_zsmul, hr, pow_one, smul_add, smul_comm a l r, smul_comm b l s]

theorem eq_zero_of_dv {t : Tate l M} (h : ∀ k, Dv k t) : t = 0 := by
  refine Tate.ext fun k => ?_
  show t.lev k = 1
  obtain ⟨s, hs⟩ := h k
  rw [hs, lev_nsmul, Tate.lev_pow]

theorem dv_two_of_lev {w : Tate l M} (h : w.lev 2 = 1) : Dv 2 w := by
  refine ⟨Tate.mk (fun n => w.lev (n + 2)) fun n => ⟨?_, ?_⟩, ?_⟩
  · rw [add_comm, Tate.lev_add_pow, h]
  · exact Tate.lev_succ w (n + 2)
  · refine Tate.ext fun n => ?_
    rw [lev_nsmul, Tate.lev_mk, Tate.lev_add_pow]

end Lemmas

end GlobalTheory.MinkowskiTate

namespace GlobalTheory.MinkowskiTate

section Endo

variable {l : ℕ} [Fact l.Prime] {M : Type} [CommGroup M]

theorem dv_pow_sub (k : ℕ) {u : Module.End ℤ_[l] (Tate l M)} (h : ∀ t, Dv k (u t - t)) (n : ℕ) :
    ∀ t, Dv k ((u ^ n) t - t) := by
  induction n with
  | zero => intro t; rw [pow_zero, Module.End.one_apply, sub_self]; exact dv_zero k
  | succ n ih =>
    intro t
    rw [pow_succ', Module.End.mul_apply]
    have e : u ((u ^ n) t) - t = (u ((u ^ n) t) - (u ^ n) t) + ((u ^ n) t - t) := by abel
    rw [e]
    exact dv_add (h _) (ih t)

theorem dv_succ_of_pow_eq_one {q : ℕ} (hq : q.Prime) {v : Module.End ℤ_[l] (Tate l M)}
    (hv : v ^ q = 1) {k : ℕ} (hk : 2 ≤ k) (h : ∀ t, Dv k (v t - t)) (t : Tate l M) :
    Dv (k + 1) (v t - t) := by
  set D := v - 1 with hD
  have hDt : ∀ t, D t = v t - t := fun t => by
    rw [hD, LinearMap.sub_apply, Module.End.one_apply]
  have hmap : ∀ a t, Dv a t → Dv (a + k) (D t) := by
    rintro a _ ⟨s, rfl⟩
    obtain ⟨r, hr⟩ := h s
    refine ⟨r, ?_⟩
    rw [map_nsmul, hDt, hr, pow_add, smul_smul]
  have hpow : ∀ j t, Dv (j * k) ((D ^ j) t) := by
    intro j
    induction j with
    | zero => intro t; exact ⟨t, by rw [pow_zero, Module.End.one_apply, zero_mul, pow_zero, one_smul]⟩
    | succ j ih =>
      intro t
      rw [pow_succ', Module.End.mul_apply, Nat.succ_mul]
      exact hmap _ _ (ih t)
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 + 1 := ⟨q - 2, by have := hq.two_le; omega⟩
  have hvD : v = D + 1 := by rw [hD, sub_add_cancel]
  have key := congrArg (fun f : Module.End ℤ_[l] (Tate l M) => f t) hv
  rw [hvD, (Commute.one_right D).add_pow, Finset.sum_range_succ', Finset.sum_range_succ'] at key
  simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply,
    one_pow, _root_.mul_one, Module.End.natCast_apply, map_nsmul, pow_zero, Nat.choose_zero_right,
    Nat.choose_one_right, pow_one, Module.End.one_apply, one_smul, zero_add, Nat.cast_one] at key
  have hS : Dv (k + 2) (∑ x ∈ Finset.range (r + 1),
      (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) :=
    dv_sum _ _ fun x _ => dv_nsmul _ (dv_mono (by nlinarith) (hpow (x + 1 + 1) t))
  have hqD : (r + 1 + 1) • D t = -(∑ x ∈ Finset.range (r + 1),
      (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) := by
    calc (r + 1 + 1) • D t = ((∑ x ∈ Finset.range (r + 1),
          (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) + (r + 1 + 1) • D t + t) - t -
          (∑ x ∈ Finset.range (r + 1), (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) := by
          abel
      _ = t - t - (∑ x ∈ Finset.range (r + 1),
          (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) := by rw [key]
      _ = _ := by abel
  have hq2 : Dv (k + 2) ((r + 1 + 1) • D t) := hqD ▸ dv_neg hS
  obtain ⟨s, hs⟩ := h t
  rw [hDt, hs, smul_comm (r + 1 + 1) (l ^ k) s] at hq2
  have h2 : Dv 2 ((r + 1 + 1) • s) := dv_of_pow_nsmul hq2
  have h1 : Dv 1 s := by
    by_cases hql : r + 1 + 1 = l
    · rw [hql] at h2
      exact dv_of_pow_nsmul (a := 1) (b := 1) (by rw [pow_one]; exact h2)
    · exact dv_one_of_nsmul ((Nat.coprime_primes hq Fact.out).2 hql) (dv_mono (by norm_num) h2)
  obtain ⟨r', hr'⟩ := h1
  exact ⟨r', by rw [hs, hr', pow_one, smul_smul, ← pow_succ]⟩

theorem eq_one_of_prime {q : ℕ} (hq : q.Prime) {v : Module.End ℤ_[l] (Tate l M)} (hv : v ^ q = 1)
    (h : ∀ t, Dv 2 (v t - t)) : v = 1 := by
  have hall : ∀ k, 2 ≤ k → ∀ t, Dv k (v t - t) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact h
    | succ k hk ih => exact dv_succ_of_pow_eq_one hq hv hk ih
  refine LinearMap.ext fun t => ?_
  have h0 : v t - t = 0 :=
    eq_zero_of_dv fun k => dv_mono (le_max_left k 2) (hall _ (le_max_right k 2) t)
  rw [Module.End.one_apply]
  exact sub_eq_zero.1 h0

end Endo

end GlobalTheory.MinkowskiTate

theorem GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two : ∀ (l : ℕ) [Fact l.Prime] (M : Type)
    [CommGroup M] (u : Module.End ℤ_[l] (Tate l M)) (E : ℕ), 0 < E → u ^ E = 1 →
    (∀ t, (u t).lev 2 = t.lev 2) → u = 1 := by
  intro l _ M _ u E hE hu h2
  have h : ∀ t, GlobalTheory.MinkowskiTate.Dv 2 (u t - t) := fun t =>
    GlobalTheory.MinkowskiTate.dv_two_of_lev (by rw [GlobalTheory.MinkowskiTate.lev_sub, h2, mul_inv_cancel])
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    rcases Nat.lt_or_ge E 2 with hlt | hge
    · obtain rfl : E = 1 := by omega
      rwa [pow_one] at hu
    · have hq : E.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨E₁, hE₁⟩ := Nat.minFac_dvd E
      have hpos : 0 < E₁ := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hE₁; omega
      have hlt : E₁ < E := by
        have := hq.two_le
        rw [hE₁]
        nlinarith
      have hv : (u ^ E₁) ^ E.minFac = 1 := by rw [← pow_mul, mul_comm, ← hE₁, hu]
      exact ih E₁ hlt hpos (GlobalTheory.MinkowskiTate.eq_one_of_prime hq hv
        (GlobalTheory.MinkowskiTate.dv_pow_sub 2 h E₁))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharLineBundleFibreModpEqRatProjectiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerChar_lineBundle_fibre_modp_eq_rat_projective : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (D : ℕ), IsArithVar q D → ∀ (p : ℕ) [Fact p.Prime] (N : LB W), N.IsLB → (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); chi (ZMod p) (toMod (N.pull (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))))) = chi ℚ (toMod (N.pull (ratFibre.fst q))) ∧ chi (ZMod p) (structureModule (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))) = chi ℚ (structureModule (ratFibre q))) := by
  first | exact @GlobalTheory.ChiFibre.chi_fibre_eq | exact GlobalTheory.ChiFibre.chi_fibre_eq | (intros; apply GlobalTheory.ChiFibre.chi_fibre_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceComplexStructureSignaStatement
section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedeanPhaseSpace_complexStructure_signatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (ε : InfinitePlace F → ℤˣ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ (u u' u₁ : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧ (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) ∧
        (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) ∧
        (∀ w, u₁.map (piInf (τ w)) = A w * (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  first | exact @GlobalTheory.HoweD.exists_bridgeD | exact GlobalTheory.HoweD.exists_bridgeD | (intros; apply GlobalTheory.HoweD.exists_bridgeD <;> assumption)
end

