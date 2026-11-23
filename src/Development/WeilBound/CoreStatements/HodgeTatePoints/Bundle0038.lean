module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.CbBase
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0016
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsSplitIdempotentConjugation
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RiRank
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FirstPowerEqProdAt
section
noncomputable section

namespace PositivityTheory.HtPt.Cb

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open ReciprocityTheory.ChartRestriction.G.TB

section

variable {R : Type} [CommRing R] {d n : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
variable {x y z w : Pt R n d}

theorem first_form_zero_left (hy : Z y) (hz : Z z) : ev ![0, y, z] B.ph1 = 1 := by
  have hb : ZZ ![y, z] := ZZ_cons hy (ZZ_cons hz ZZ_nil)
  have h := congrArg (ev ![y, z]) B.cocycleLeft_zero_fst
  rw [ev3 hb Z_zero (Z_pt _) (Z_pt _), ep_zero hb, ev_one] at h
  simpa [ep_pt hb] using h

theorem first_form_zero_right (hy : Z y) (hz : Z z) : ev ![y, z, 0] B.ph1 = 1 := by
  have hb : ZZ ![y, z] := ZZ_cons hy (ZZ_cons hz ZZ_nil)
  have h := congrArg (ev ![y, z]) B.cocycleLeft_zero_thd
  rw [ev3 hb (Z_pt _) (Z_pt _) Z_zero, ep_zero hb, ev_one] at h
  simpa [ep_pt hb] using h

theorem first_form_comm_at (hx : Z x) (hy : Z y) (hz : Z z) : ev ![x, y, z] B.ph1 = ev ![y, x, z] B.ph1 := by
  have hb : ZZ ![x, y, z] := ZZ_cons hx (ZZ_cons hy (ZZ_cons hz ZZ_nil))
  have h := congrArg (ev ![x, y, z]) B.cocycleLeft_comm
  rw [ev3 hb (Z_pt _) (Z_pt _) (Z_pt _)] at h
  simp only [ep_pt hb] at h
  simpa using h.symm

theorem first_form_assoc_at (hx : Z x) (hy : Z y) (hw : Z w) (hz : Z z) :
    ev ![x, y, z] B.ph1 * ev ![B.G.add x y, w, z] B.ph1 = ev ![y, w, z] B.ph1 * ev ![x, B.G.add y w, z] B.ph1 := by
  have hb : ZZ ![x, y, w, z] := ZZ_cons hx (ZZ_cons hy (ZZ_cons hw (ZZ_cons hz ZZ_nil)))
  have h := congrArg (ev ![x, y, w, z]) B.cocycleLeft_assoc
  simp only [evm hb] at h
  rw [ev3 hb (Z_pt _) (Z_pt _) (Z_pt _), ev3 hb (Z_add _ (Z_pt _) (Z_pt _)) (Z_pt _) (Z_pt _),
    ev3 hb (Z_pt _) (Z_pt _) (Z_pt _), ev3 hb (Z_pt _) (Z_add _ (Z_pt _) (Z_pt _)) (Z_pt _),
    ep_add _ hb (Z_pt _) (Z_pt _), ep_add _ hb (Z_pt _) (Z_pt _)] at h
  simp only [ep_pt hb] at h
  simpa using h

private theorem fgLaw_add_comm (G : FGLaw R d) (hx : Z x) (hy : Z y) : G.add x y = G.add y x := by
  have hb : ZZ ![x, y] := ZZ_cons hx (ZZ_cons hy ZZ_nil)
  have e : G.add (pt R d 1) (pt R d 0) = (G.add (pt R d 0) (pt R d 1) : Pt R 2 d) := by
    funext i
    exact (G.comm i).trans (eval_points_two _).symm
  have h := congrArg (ep ![x, y]) e
  rw [ep_add G hb (Z_pt _) (Z_pt _), ep_add G hb (Z_pt _) (Z_pt _)] at h
  simpa [ep_pt hb] using h.symm

private theorem fgLaw_add_assoc (G : FGLaw R d) (hx : Z x) (hy : Z y) (hz : Z z) :
    G.add (G.add x y) z = G.add x (G.add y z) := by
  have hb : ZZ ![x, y, z] := ZZ_cons hx (ZZ_cons hy (ZZ_cons hz ZZ_nil))
  have e : G.add (G.add (pt R d 0) (pt R d 1)) (pt R d 2) =
      (G.add (pt R d 0) (G.add (pt R d 1) (pt R d 2)) : Pt R 3 d) := by
    funext i
    exact G.assoc i
  have h := congrArg (ep ![x, y, z]) e
  rw [ep_add G hb (Z_add _ (Z_pt _) (Z_pt _)) (Z_pt _), ep_add G hb (Z_pt _) (Z_pt _),
    ep_add G hb (Z_pt _) (Z_add _ (Z_pt _) (Z_pt _)), ep_add G hb (Z_pt _) (Z_pt _)] at h
  simpa [ep_pt hb] using h

theorem first_form_four_term {a b c e : Pt R n d} (ha : Z a) (hb : Z b) (hc : Z c) (he : Z e) (hz : Z z) :
    ev ![a, b, z] B.ph1 * ev ![c, e, z] B.ph1 * ev ![B.G.add a b, B.G.add c e, z] B.ph1 =
      ev ![a, c, z] B.ph1 * ev ![b, e, z] B.ph1 * ev ![B.G.add a c, B.G.add b e, z] B.ph1 := by
  have A1 := first_form_assoc_at B (Z_add B.G ha hb) hc he hz
  have A2 := first_form_assoc_at B ha hb hc hz
  have A3 := first_form_assoc_at B (Z_add B.G ha hc) hb he hz
  have A4 := first_form_assoc_at B ha hc hb hz
  have e1 : B.G.add c b = B.G.add b c := fgLaw_add_comm B.G hc hb
  have e2 : B.G.add (B.G.add a c) b = B.G.add (B.G.add a b) c := by
    rw [fgLaw_add_assoc B.G ha hc hb, e1, ← fgLaw_add_assoc B.G ha hb hc]
  rw [e1, first_form_comm_at B hc hb hz] at A4
  rw [e2] at A3
  linear_combination ev ![B.G.add (B.G.add a b) c, e, z] B.ph1 * A2 -
    ev ![B.G.add (B.G.add a b) c, e, z] B.ph1 * A4 - ev ![a, b, z] B.ph1 * A1 + ev ![a, c, z] B.ph1 * A3

theorem first_power_eq_prod_at (hx : Z x) (hz : Z z) (k : ℕ) :
    ev ![x, z] (pow1 B k) = ∏ j ∈ Finset.range k, ev ![comp1 (B.A.act (j : O)) x, x, z] B.ph1 := by
  rw [pow1]
  have hb : ZZ ![x, z] := ZZ_cons hx (ZZ_cons hz ZZ_nil)
  rw [evprod hb]
  apply Finset.prod_congr rfl
  intro j _
  rw [ev3 hb (Z_comp1 (Z_act _ _) (Z_pt _)) (Z_pt _) (Z_pt _),
    ep_comp1 _ hb (Z_pt _), ep_pt hb, ep_pt hb]
  rfl

private theorem comp1_act_natCast_zero (hx : Z x) : comp1 (B.A.act ((0 : ℕ) : O)) x = 0 := by
  rw [Nat.cast_zero, act_zero]
  funext i
  exact evz (ZZ_cons hx ZZ_nil)

private theorem comp1_act_natCast_succ (hx : Z x) (k : ℕ) :
    comp1 (B.A.act ((k + 1 : ℕ) : O)) x = B.G.add (comp1 (B.A.act (k : O)) x) x := by
  rw [Nat.cast_succ, PositivityTheory.HtPt.Cb.add_act B.A _ _ hx, B.A.one_act]
  congr 1
  exact ep_pt (ZZ_cons hx ZZ_nil) 0

private theorem ev_pow1_succ (hx : Z x) (hz : Z z) (k : ℕ) :
    ev ![x, z] (pow1 B (k + 1)) = ev ![x, z] (pow1 B k) * ev ![comp1 (B.A.act (k : O)) x, x, z] B.ph1 := by
  rw [first_power_eq_prod_at B hx hz, first_power_eq_prod_at B hx hz, Finset.prod_range_succ]

theorem first_power_add_at (hx : Z x) (hy : Z y) (hz : Z z) (k : ℕ) :
    ev ![B.G.add x y, z] (pow1 B k) * ev ![x, y, z] B.ph1 ^ k =
      ev ![x, z] (pow1 B k) * ev ![y, z] (pow1 B k) *
        ev ![comp1 (B.A.act (k : O)) x, comp1 (B.A.act (k : O)) y, z] B.ph1 := by
  induction k with
  | zero =>
    rw [first_power_eq_prod_at B (Z_add B.G hx hy) hz, first_power_eq_prod_at B hx hz, first_power_eq_prod_at B hy hz, Finset.prod_range_zero,
      comp1_act_natCast_zero B hx, comp1_act_natCast_zero B hy, first_form_zero_left B Z_zero hz]
    simp
  | succ k ih =>
    have hkx : Z (comp1 (B.A.act (k : O)) x) := Z_comp1 (Z_act _ _) hx
    have hky : Z (comp1 (B.A.act (k : O)) y) := Z_comp1 (Z_act _ _) hy
    have h4 := first_form_four_term B hkx hky hx hy hz
    rw [ev_pow1_succ B (Z_add B.G hx hy) hz, ev_pow1_succ B hx hz, ev_pow1_succ B hy hz,
      comp1_act_natCast_succ B hx, comp1_act_natCast_succ B hy, act_add B.A _ hx hy]
    linear_combination ev ![x, y, z] B.ph1 *
        ev ![B.G.add (comp1 (B.A.act (k : O)) x) (comp1 (B.A.act (k : O)) y), B.G.add x y, z] B.ph1 * ih +
      ev ![x, z] (pow1 B k) * ev ![y, z] (pow1 B k) * h4

theorem adjoint_law_first_at (a : O) (hx : Z x) (hy : Z y) (hz : Z z) :
    ev ![comp1 (B.A.act a) x, comp1 (B.A.act a) y, z] B.ph1 * ev ![B.G.add x y, z] (B.ad a) =
      ev ![x, z] (B.ad a) * ev ![y, z] (B.ad a) * ev ![x, y, comp1 (B.A.act (star a)) z] B.ph1 := by
  have hb : ZZ ![x, y, z] := ZZ_cons hx (ZZ_cons hy (ZZ_cons hz ZZ_nil))
  have h := congrArg (ev ![x, y, z]) (B.adjoint_compat_left a)
  simp only [evm hb] at h
  rw [ev3 hb (Z_comp1 (Z_act _ _) (Z_pt _)) (Z_comp1 (Z_act _ _) (Z_pt _)) (Z_pt _),
    ev2 hb (Z_add _ (Z_pt _) (Z_pt _)) (Z_pt _), ev2 hb (Z_pt _) (Z_pt _), ev2 hb (Z_pt _) (Z_pt _),
    ev3 hb (Z_pt _) (Z_pt _) (Z_comp1 (Z_act _ _) (Z_pt _)),
    ep_comp1 _ hb (Z_pt _), ep_comp1 _ hb (Z_pt _), ep_comp1 _ hb (Z_pt _),
    ep_add _ hb (Z_pt _) (Z_pt _)] at h
  simp only [ep_pt hb] at h
  simpa using h

theorem ad_zero_left (a : O) (hz : Z z) : ev ![0, z] (B.ad a) = 1 := by
  have hb : ZZ ![z] := ZZ_cons hz ZZ_nil
  have h := congrArg (ev ![z]) (B.adjoint_zero_fst a)
  rw [ev2 hb Z_zero (Z_pt _), ep_zero hb, ev_one] at h
  simpa [ep_pt hb] using h

theorem first_power_adjoint_at (a : O) (hx : Z x) (hz : Z z) (k : ℕ) :
    ev ![comp1 (B.A.act a) x, z] (pow1 B k) * ev ![comp1 (B.A.act (k : O)) x, z] (B.ad a) =
      ev ![x, z] (B.ad a) ^ k * ev ![x, comp1 (B.A.act (star a)) z] (pow1 B k) := by
  induction k with
  | zero =>
    rw [first_power_eq_prod_at B (Z_comp1 (Z_act _ _) hx) hz, first_power_eq_prod_at B hx (Z_comp1 (Z_act _ _) hz), Finset.prod_range_zero,
      Finset.prod_range_zero, comp1_act_natCast_zero B hx, ad_zero_left B a hz]
    simp
  | succ k ih =>
    have hkx : Z (comp1 (B.A.act (k : O)) x) := Z_comp1 (Z_act _ _) hx
    have law := adjoint_law_first_at B a hkx hx hz
    rw [ev_pow1_succ B (Z_comp1 (Z_act _ _) hx) hz, ev_pow1_succ B hx (Z_comp1 (Z_act _ _) hz),
      comp1_act_natCast_succ B hx, act_comm B.A (k : O) a hx]
    linear_combination ev ![comp1 (B.A.act a) x, z] (pow1 B k) * law +
      ev ![x, z] (B.ad a) * ev ![comp1 (B.A.act (k : O)) x, x, comp1 (B.A.act (star a)) z] B.ph1 * ih

theorem first_power_zero_left (hz : Z z) (k : ℕ) : ev ![0, z] (pow1 B k) = 1 := by
  rw [first_power_eq_prod_at B Z_zero hz]
  apply Finset.prod_eq_one
  intro j _
  rw [germComp1_zero_of_noConstantCoeff (Z_act _ _)]
  exact first_form_zero_left B Z_zero hz

theorem first_power_zero_right (hx : Z x) (k : ℕ) : ev ![x, 0] (pow1 B k) = 1 := by
  rw [first_power_eq_prod_at B hx Z_zero]
  exact Finset.prod_eq_one fun j _ => first_form_zero_right B (Z_comp1 (Z_act _ _) hx) hx

end

theorem first_power_add : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), ev (n := 3) ![B.G.add (pt R d 0) (pt R d 1), pt R d 2] (pow1 B n) * B.ph1 ^ n = ev (n := 3) ![pt R d 0, pt R d 2] (pow1 B n) * ev (n := 3) ![pt R d 1, pt R d 2] (pow1 B n) * ev (n := 3) ![comp1 (B.A.act (n : O)) (pt R d 0), comp1 (B.A.act (n : O)) (pt R d 1), pt R d 2] B.ph1 := by
  intro R _ d O _ _ B n
  have h := first_power_add_at B (Z_pt (n := 3) 0) (Z_pt 1) (Z_pt 2) n
  rwa [eval_points_three] at h

theorem first_power_adjoint : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (n : ℕ), ev (n := 2) ![comp1 (B.A.act a) (pt R d 0), pt R d 1] (pow1 B n) * ev (n := 2) ![comp1 (B.A.act (n : O)) (pt R d 0), pt R d 1] (B.ad a) = B.ad a ^ n * ev (n := 2) ![pt R d 0, comp1 (B.A.act (star a)) (pt R d 1)] (pow1 B n) := by
  intro R _ d O _ _ B a n
  have h := first_power_adjoint_at B a (Z_pt (n := 2) 0) (Z_pt 1) n
  rwa [eval_points_two] at h

end PositivityTheory.HtPt.Cb
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.PflagZ
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.HtPt.Pflag

def idxList {N : ℕ} (α : Fin N → ℕ) : List (Fin N) :=
  (List.finRange N).flatMap fun i => List.replicate (α i) i

theorem count_idxList {N : ℕ} (α : Fin N → ℕ) (j : Fin N) : (idxList α).count j = α j := by
  classical
  simp only [idxList, List.count_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp [List.count_replicate]

theorem length_idxList {N : ℕ} (α : Fin N → ℕ) : (idxList α).length = ∑ i, α i := by
  simp only [idxList, List.length_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp

theorem map_idxList {K : Type} {N : ℕ} (x : Fin N → K → ℤ) (α : Fin N → ℕ) :
    (idxList α).map x = rootList x α := by
  simp [idxList, rootList, List.map_flatMap, List.map_replicate]

theorem prod_map_X {σ : Type} [DecidableEq σ] (s : Multiset σ) :
    ((s.map X).prod : MvPolynomial σ ℝ) = monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, map_add (f := _),
      Multiset.toFinsupp_singleton, X, monomial_mul, one_mul]

theorem length_classList_of_hom {K σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {m : ℕ}
    (hH : H.IsHomogeneous m) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) : (classList cls μ).length = m := by
  classical
  have h := hH (mem_support_iff.mp hμ)
  simp only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
  rw [← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem isHomogeneous_hsymm_real (N a : ℕ) : (hsymm (Fin N) ℝ a).IsHomogeneous a := by
  classical
  apply IsHomogeneous.sum
  intro s _
  rw [prod_map_X]
  apply isHomogeneous_monomial
  have h := Finsupp.card_toMultiset (Multiset.toFinsupp (s : Multiset (Fin N)))
  rw [Multiset.toFinsupp_toMultiset] at h
  calc Finsupp.degree (Multiset.toFinsupp (s : Multiset (Fin N)))
      = (Multiset.toFinsupp (s : Multiset (Fin N))).sum fun _ => id := rfl
    _ = a := by rw [← h]; simp

section
variable (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
  [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F))

theorem genNum_hsymm {N : ℕ} (x : Fin N → K → ℤ) (a : ℕ) (Q : List (K → ℤ)) :
    genNum F V x (hsymm (Fin N) ℝ a) Q =
      ((∑ α ∈ Finset.Nat.antidiagonalTuple N a, intNumL F V (rootList x α ++ Q) : ℤ) : ℝ) := by
  classical
  rw [hsymm, (genNum_linear F K ι (Fin N) V x Q).2.2.1]
  simp_rw [prod_map_X, (genNum_linear F K ι (Fin N) V x Q).2.2.2, one_mul]
  push_cast
  symm
  refine Finset.sum_bij'
    (fun α hα => (⟨(idxList α : Multiset (Fin N)), by
      rw [Multiset.coe_card, length_idxList, (Finset.Nat.mem_antidiagonalTuple.mp hα)]⟩ : Sym (Fin N) a))
    (fun s _ => fun i => (s : Multiset (Fin N)).count i) ?_ ?_ ?_ ?_ ?_
  · intro α _
    exact Finset.mem_univ _
  · intro s _
    rw [Finset.Nat.mem_antidiagonalTuple]
    rw [← Finset.sum_subset (Finset.subset_univ (s : Multiset (Fin N)).toFinset)]
    · rw [Multiset.toFinset_sum_count_eq]
      exact s.2
    · intro i _ hi
      simpa using hi
  · intro α _
    funext i
    simp [Multiset.coe_count, count_idxList]
  · intro s _
    apply Subtype.ext
    ext i
    simp [Multiset.coe_count, count_idxList]
  · intro α _
    rw [intNumL_perm_of_perm F K ι V (rootList x α ++ Q) _]
    apply List.Perm.append_right
    rw [← map_idxList]
    rw [← Multiset.coe_eq_coe]
    simp [classList, Multiset.toFinsupp_toMultiset]

theorem genNum_neg (d : ℕ) (hV : IsMultiProjPrime V)
    (hd : ringKrullDim (MRing ι F ⧸ V) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) {N : ℕ}
    (b : Fin N → K → ℤ) (H : MvPolynomial (Fin N) ℝ) (m : ℕ) (hH : H.IsHomogeneous m)
    (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    genNum F V b (aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) H) Q =
      genNum F V (fun i => -b i) H Q := by
  classical
  have h := genNum_linear_subst F K ι V d hV hd (Fin N) (Fin N) b
    (fun t i => if t = i then -1 else 0) H m hH Q hQ
  have e1 : (fun t : Fin N => ∑ i : Fin N, (if t = i then (-1 : ℤ) else 0) • b i) =
      fun t => -b t := by
    funext t
    simp
  have e2 : (fun t : Fin N => ∑ i : Fin N,
      C (((if t = i then (-1 : ℤ) else 0 : ℤ) : ℝ)) * (X i : MvPolynomial (Fin N) ℝ)) =
      fun t => (-X t : MvPolynomial (Fin N) ℝ) := by
    funext t
    simp only [apply_ite (fun z : ℤ => ((z : ℝ))), Int.cast_neg, Int.cast_one, Int.cast_zero,
      apply_ite C, map_neg, map_one, map_zero, ite_mul, neg_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ t (fun i => -(X i : MvPolynomial (Fin N) ℝ))]
    simp
  rw [e1, e2] at h
  exact h.symm

end

end PositivityTheory.HtPt.Pflag
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.ProdDigits
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Pmono

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
lemma mem_xIdeal (M : Submodule R (F → C)) (χ : MulChar F R) (r : R) :
    r ∈ xIdeal M χ ↔ (fun a => algebraMap R C (r * χ a)) ∈ M := by
  have : (fun a => algebraMap R C (r * χ a)) = r • fun a => algebraMap R C (χ a) := by
    funext a
    simp [Algebra.smul_def]
  rw [this]
  rfl

lemma pow_mem (AA : HopfOrder (C := C) R F) {g : F → C} (hg : g ∈ AA.carrier) (k : ℕ) :
    g ^ k ∈ AA.carrier := by
  induction k with
  | zero => rw [pow_zero]; exact AA.one_mem
  | succ k ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hg

lemma mono_mem (AA : HopfOrder (C := C) R F) (σ : MulChar F R) {p f : ℕ} (hp : p ≠ 0)
    (c : ℕ → R) (hc : ∀ n, c n ∈ xIdeal AA.carrier (σ ^ p ^ n)) (e : Fin f → ℕ)
    (he : ∑ n : Fin f, e n * p ^ (n : ℕ) ≠ 0) :
    ∏ n : Fin f, c n ^ e n ∈ xIdeal AA.carrier (σ ^ (∑ n : Fin f, e n * p ^ (n : ℕ))) := by
  rw [mem_xIdeal]
  have hmem : (∏ n : Fin f, (fun a => algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a)) ^ e n) ∈
      AA.carrier :=
    Finset.prod_induction _ (fun g => g ∈ AA.carrier) (fun a b ha hb => AA.mul_mem a b ha hb)
      AA.one_mem fun n _ => pow_mem AA ((mem_xIdeal _ _ _).1 (hc n)) _
  have hfun : (fun a => algebraMap R C ((∏ n : Fin f, c n ^ e n) *
      (σ ^ (∑ n : Fin f, e n * p ^ (n : ℕ))) a)) =
      ∏ n : Fin f, (fun a => algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a)) ^ e n := by
    funext a
    rw [Finset.prod_apply, MulChar.pow_apply' _ he, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [Pi.pow_apply, MulChar.pow_apply' _ (pow_ne_zero _ hp), ← map_pow (algebraMap R C), mul_pow,
      ← pow_mul,
      mul_comm (e n)]
  rw [hfun]
  exact hmem

end

lemma prod_digits {p f : ℕ} (hp : p ≠ 0) (w : ℕ → NNReal) :
    (∏ d : Fin f → Fin p, if ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = 0 then 1
      else w (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) = ∏ m ∈ Finset.Icc 1 (p ^ f - 1), w m := by
  have h1 : (∏ d : Fin f → Fin p, if ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = 0 then 1
      else w (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) =
      ∏ i : Fin (p ^ f), if (i : ℕ) = 0 then 1 else w i :=
    Fintype.prod_equiv finFunctionFinEquiv _ _ fun d => by rw [finFunctionFinEquiv_apply]
  have hq : 0 < p ^ f := pow_pos (Nat.pos_of_ne_zero hp) _
  have h2 : Finset.range (p ^ f) = insert 0 (Finset.Icc 1 (p ^ f - 1)) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [h1, Fin.prod_univ_eq_prod_range (fun i => if i = 0 then 1 else w i), h2,
    Finset.prod_insert (by simp), if_pos rfl, one_mul]
  refine Finset.prod_congr rfl fun m hm => if_neg ?_
  have := (Finset.mem_Icc.1 hm).1
  omega

theorem r_mono : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → (∀ n, v (p : C) ≤ v (algebraMap R C (c n)) ^ (p - 1)) ∧ ∀ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) → xIdeal AA.carrier (σ ^ (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) = Ideal.span {∏ n : Fin f, c n ^ (d n : ℕ)} := by
  intro p hpp C _ _ _ v R _ _ hv hvp F _ _ _ _ f hf AA hst σ hσ c hc
  have hp0 : p ≠ 0 := hpp.out.ne_zero
  obtain ⟨AD, hstD, hcol, hfund⟩ := rank_one_sum p C v R hv hvp F f hf AA hst
  obtain ⟨-, -, hpow, -, -⟩ := GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hvp F f hf σ hσ
  choose g hg0 hg using fun m : ℕ => (eig_rank_one p C v R hv hvp F f hf AA hst (σ ^ m)).1
  choose gD hgD0 hgD using fun m : ℕ => (eig_rank_one p C v R hv hvp F f hf AD hstD (σ ^ m)).1
  have hx : ∀ n : ℕ, (v (algebraMap R C (c n)) * v (algebraMap R C (gD (p ^ n)))) ^ (p - 1) =
      v (p : C) := fun n => hfund (σ ^ p ^ n) (hpow n) _ _ (hc n) (hgD _)
  have hle : ∀ (BB : HopfOrder (C := C) R F) (γ b : ℕ → R),
      (∀ m, xIdeal BB.carrier (σ ^ m) = Ideal.span {γ m}) →
      (∀ n, xIdeal BB.carrier (σ ^ p ^ n) = Ideal.span {b n}) →
      ∀ d : Fin f → Fin p, ∏ n : Fin f, v (algebraMap R C (b n)) ^ (d n : ℕ) ≤
        if ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = 0 then 1
        else v (algebraMap R C (γ (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ)))) := by
    intro BB γ b hγ hb d
    split_ifs with h
    · exact Finset.prod_le_one' fun n _ => pow_le_one' (hv.map_le_one _) _
    · have hm := mono_mem BB σ hp0 b
        (fun n => by rw [hb n]; exact Ideal.mem_span_singleton_self _) (fun n => (d n : ℕ)) h
      rw [hγ, Ideal.mem_span_singleton, hv.dvd_iff_le] at hm
      simpa only [map_prod, map_pow] using hm
  refine ⟨fun n => ?_, fun d hd => ?_⟩
  · rw [← hx n]
    exact pow_le_pow_left' (mul_le_of_le_one_right' (hv.map_le_one _)) _
  · have hN := (PositivityTheory.HtPt.Ri.r_decomp p C v R hv hvp F f hf AA hst σ hσ g hg).2.2
    have hD := (PositivityTheory.HtPt.Ri.r_decomp p C v R hv hvp F f hf AD hstD σ hσ gD hgD).2.2
    have hP : v (p : C) ≠ 0 := by
      rw [Ne, map_eq_zero]
      exact_mod_cast hp0
    have key := (count p f hpp.out.two_le (v (p : C)) hP (fun n => v (algebraMap R C (c n)))
      (fun n => v (algebraMap R C (gD (p ^ (n : ℕ))))) _ _ (fun n => hx n) (hle AA g c hg hc)
      (hle AD gD (fun n => gD (p ^ n)) hgD fun n => hgD _)
      (by
        rw [Finset.prod_mul_distrib, prod_digits hp0 fun m => v (algebraMap R C (g m)),
          prod_digits hp0 fun m => v (algebraMap R C (gD m))]
        exact hcol _ _ hN hD) d).1
    have hne : ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) ≠ 0 := by
      obtain ⟨n, hn⟩ := hd
      intro h
      exact mul_ne_zero hn (pow_ne_zero _ hp0)
        (Finset.sum_eq_zero_iff.1 h n (Finset.mem_univ n))
    rw [if_neg hne] at key
    rw [hg]
    have hval : v (algebraMap R C (∏ n : Fin f, c n ^ (d n : ℕ))) =
        v (algebraMap R C (g (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ)))) := by
      rw [key]
      simp only [map_prod, map_pow]
    exact le_antisymm (Ideal.span_singleton_le_span_singleton.2 (hv.dvd_of_le hval.ge))
      (Ideal.span_singleton_le_span_singleton.2 (hv.dvd_of_le hval.le))

end PositivityTheory.HtPt.Pmono
end

