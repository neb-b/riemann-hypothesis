module

public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Bundle0002
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.WeylComplementDetCoeffSpan
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.EvalIdFrameRowAct

@[expose] public section

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.BranchingSourceIdentity
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions.G.LatticeSystems

section Cast

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (N : ℕ) (hm : P.m + 1 = N)

def emC (b : GlobalTheory P) (v : Fin N × Fin N) : (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) :=
  emP P b (Fin.cast hm.symm v.1, Fin.cast hm.symm v.2)

def gamC (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (b : GlobalTheory P) : Matrix (Fin N) (Fin N) Kf :=
  (gam P g b).submatrix (Fin.cast hm.symm) (Fin.cast hm.symm)

def nuC (b : GlobalTheory P) : Fin N → ℕ := fun t => nuB P b (Fin.cast hm.symm t)

variable (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (hg : ∀ v, IsUnit (g v).det)

include hg in
theorem htupW_leC (hinj : Function.Injective (algebraMap O Kf)) (T : Submodule O P.Xsp)
    (hT : ∀ F : GlobalTheory P → MvPolynomial (Fin N × Fin N) Kf,
      (∀ b, F b ∈ deltaL O Kf N (nuC P N hm b) (gamC P N hm g b)) →
        (∏ b : GlobalTheory P, (gamC P N hm g b).det ^ (-(eB P b))) • ∏ b, rename (emC P N hm b) (F b) ∈ T) :
    P.HtupW (fun v => colSpan (P.W v) (g v)) ≤ T := by
  subst hm
  exact htupW_le P g hg hinj T hT

include hg in
theorem mem_htupWC (hinj : Function.Injective (algebraMap O Kf)) (F : GlobalTheory P → MvPolynomial (Fin N × Fin N) Kf)
    (hF : ∀ b, F b ∈ deltaL O Kf N (nuC P N hm b) (gamC P N hm g b)) :
    (∏ b : GlobalTheory P, (gamC P N hm g b).det ^ (-(eB P b))) • ∏ b, rename (emC P N hm b) (F b) ∈
      P.HtupW (fun v => colSpan (P.W v) (g v)) := by
  subst hm
  exact mem_htupW P g hg hinj F hF

end Cast

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem branching_source_identity : XBrS := by
  intro p _ X hinj j L g hg hL T hT
  cases j with
  | zero =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact htupW_leC X.G.P _ (rankJ X 0) g hg hinj T hT
  | succ j =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact htupW_leC (X.Fl.Pj (j + 1)) _ (rankJ X (j + 1)) g hg hinj T hT

theorem branching_target_identity : XBrT := by
  intro p _ X hinj j L g hg hL F hF
  cases j with
  | zero =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact mem_htupWC X.G.P _ (rankJ X 0) g hg hinj F hF
  | succ j =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact mem_htupWC (X.Fl.Pj (j + 1)) _ (rankJ X (j + 1)) g hg hinj F hF

end Formalism.L2.PairingIndexBounds.Ent
end
end

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.FrameEdgeIdentityHolds
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def dgQ (K : Type) [Field K] (p k r : ℕ) : Matrix (Fin k) (Fin k) K := Matrix.diagonal fun c => if c.val < r then (p : K)⁻¹ else 1

theorem dgQ_det_ne (K : Type) [Field K] (p k r : ℕ) (hp : (p : K) ≠ 0) : (dgQ K p k r).det ≠ 0 := by
  unfold dgQ
  rw [Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun c _ => ?_
  split_ifs
  · exact inv_ne_zero hp
  · exact one_ne_zero

theorem mF_dgQ (j : ℕ) (b : BX X) (i0 : X.Pl → ℕ) :
    mF X (j + 1) b (dgQ (X.G.P.Qq b.1) p _ (i0 b.1)) = DgX X X.G.Kf j i0 b.1 := by
  unfold mF dgQ DgX
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, if_pos rfl]
    have : ((finCongr (rank_eq X (j + 1)).symm) a).val = a.val := rfl
    rw [this]
    split_ifs
    · rw [map_inv₀, map_inv₀, map_natCast, map_natCast]
    · rw [map_one, map_one]
  · rw [if_neg hac, if_neg (fun h => hac ((finCongr (rank_eq X (j + 1)).symm).injective h)), map_zero, map_zero]

theorem frame_edge_identity_holds : XEdge := by
  intro p _ X j L' L'' i0 h2 h4
  have key : ∀ v : X.Pl, ∃ g' h' : GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v),
      X.latAt v (j + 1) L'' = colSpan (X.G.P.W v) (g' : Matrix _ _ (X.G.P.Qq v)) ∧
      X.latAt v (j + 1) L' = colSpan (X.G.P.W v) (h' : Matrix _ _ (X.G.P.Qq v)) ∧
      (h' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) =
        (g' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) *
          dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v) := by
    intro v
    have hS := X.G.P.setting v
    have := hS.frac_alt
    have hp0 : (p : X.G.P.Qq v) ≠ 0 := pQ_ne hS.p_unif
    rcases h4 v with ⟨h0, hL⟩ | ⟨_, he⟩
    · obtain ⟨g, hg, hgL⟩ := h2 v
      have h0' : i0 v = 0 := h0
      refine ⟨Matrix.nonsingInvUnit g hg, Matrix.nonsingInvUnit g hg, ?_, hgL, ?_⟩
      · show L'' v = _
        rw [hL]; exact hgL
      · have : dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v) = 1 := by
          unfold dgQ
          rw [h0']
          simp
        rw [this, mul_one]
    · obtain ⟨g, hg, hsrc, htgt⟩ := Formalism.L2.G.Model.edgeBasis hS _ _ _ he
      have hd : IsUnit (g * dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v)).det := by
        rw [Matrix.det_mul]
        exact hg.mul (isUnit_iff_ne_zero.2 (dgQ_det_ne _ _ _ _ hp0))
      exact ⟨Matrix.nonsingInvUnit g hg, Matrix.nonsingInvUnit _ hd, hsrc, htgt, rfl⟩
  choose g' h' h1 h2' h3 using key
  refine ⟨g', h', h1, h2', fun b => ?_⟩
  rw [h3 b.1, ← mF_dgQ X j b i0]
  unfold mF
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  exact Matrix.map_mul (f := (X.G.P.ι b.1).comp (X.G.P.σ b.1 ^ b.2.val : X.G.P.Qq b.1 ≃+* X.G.P.Qq b.1).toRingHom)

end Formalism.L2.PairingIndexBounds.Ent
end
end

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.RowActSrcN
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem evX_gX {K : Type} [CommRing K] {n : ℕ} (x : ℕ × Fin n → K) (a : Fin n) (i : ℕ) : evX x (gX K n a i) = C (x (i, a)) := by
  unfold evX gX
  rw [coe_eval₂Hom, eval₂_X]

theorem evX_gY {K : Type} [CommRing K] {n : ℕ} (x : ℕ × Fin n → K) : (gY K n).map (evX x) = yV K n := by
  ext a t
  rw [Matrix.map_apply]
  unfold evX gY yV
  rw [coe_eval₂Hom, eval₂_C]
  rfl

theorem evX_HgX (j : ℕ) (b : BX X) (x : ℕ × Fin (NJ X j) → X.G.Kf) :
    evX x (HgX X X.G.Kf j b) = srcN X j b fun a i => x (i, a) := by
  unfold HgX srcN
  split_ifs with ho
  · rw [map_hvO, evX_gY]
    simp only [evX_gX]
  · rw [map_mul, map_pow, RingHom.map_det, map_hvE, evX_gY, map_pow, RingHom.map_det]
    simp only [evX_gX]
    congr 3
    ext a i
    simp [evX_gX]

theorem HgX_map (O K : Type) [CommRing O] [CommRing K] (f : O →+* K) (j : ℕ) (b : BX X) :
    map (map f) (HgX X O j b) = HgX X K j b := by
  have hx : ∀ a i, (map (map f) : GenR O (NJ X j) →+* GenR K (NJ X j)) (gX O (NJ X j) a i) = gX K (NJ X j) a i := by
    intro a i
    unfold gX
    rw [map_X]
  have hy : (gY O (NJ X j)).map (map (map f) : GenR O (NJ X j) →+* GenR K (NJ X j)) = gY K (NJ X j) := by
    ext a t
    rw [Matrix.map_apply]
    unfold gY
    rw [map_C, map_X]
  unfold HgX
  split_ifs with ho
  · rw [map_hvO, hy]
    simp only [hx]
  · rw [map_mul, map_pow, RingHom.map_det, map_hvE, hy]
    simp only [hx]
    congr 3
    ext a i
    simp [hx]

theorem hQX (hS : XShape) (j : ℕ) (b : BX X) :
    (weyl X.G.O (NJ X j) (NJ X j) le_rfl (nuM X j b)).map (toK X.G.O X.G.Kf) ≤
      Submodule.span X.G.O (Set.range fun m => AddMonoidAlgebra.coeff (HgX X X.G.Kf j b) m) := by
  obtain ⟨h1, -, hanti, hle, -, -, -, -, -, -⟩ := hS p X j b
  rw [h1]
  have key : weyl X.G.O (NJ X j) (NJ X j) le_rfl (nuS X j b) ≤
      Submodule.span X.G.O (Set.range fun m => AddMonoidAlgebra.coeff (HgX X X.G.O j b) m) := by
    by_cases ho : IsOddPos b.2
    · have hn : nuS X j b = fun t => cX X j b - muX X j (NJ X j) b t.rev := if_pos ho
      unfold HgX
      rw [if_pos ho, hn]
      exact weyl_complement_det_coeff_span X.G.O (NJ X j) _ (hanti _) _ (hle _)
    · have hn : nuS X j b = fun t => muX X j (NJ X j) b t - eX X j b := if_neg ho
      unfold HgX
      rw [if_neg ho]
      refine weyl_lattice_det_coeff_span X.G.O (NJ X j) (nuS X j b) ?_ _ _ ?_
      · rw [hn]
        exact fun a c hac => Nat.sub_le_sub_right (hanti _ hac) _
      · rw [hn]
        exact fun t => (Nat.sub_le _ _).trans (hle _ t)
  refine (Submodule.map_mono key).trans ?_
  rw [Submodule.map_span, ← Set.range_comp]
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  refine ⟨m, ?_⟩
  show _ = map (algebraMap X.G.O X.G.Kf) (AddMonoidAlgebra.coeff (HgX X X.G.O j b) m)
  rw [← HgX_map X X.G.O X.G.Kf (algebraMap X.G.O X.G.Kf) j b]
  exact coeff_map _ _ _

end Formalism.L2.PairingIndexBounds.Ent
end
end

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.XShape
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

namespace FrameShapeLemmas

theorem shape_even (m₀ n : ℕ) (hm : m₀ + 1 = n) (lam : Fin (m₀ + 1) → ℤ) (hanti : Antitone lam) (ν : ℕ → ℤ) (w : ℤ)
    (hlam : ∀ i : Fin (m₀ + 1), ν (i.val + 1) = lam i + w) (hnn : ∀ i, 0 ≤ ν i) (t : Fin n) :
    nuOf lam (Fin.cast hm.symm t) = (ν (t.val + 1)).toNat - (ν n).toNat := by
  subst hm
  have h1 := hlam t
  have h2 := hlam (Fin.last m₀)
  have h3 : lam (Fin.last m₀) ≤ lam t := hanti (Fin.le_last t)
  have h4 := hnn (t.val + 1)
  have h5 := hnn (m₀ + 1)
  rw [Fin.val_last] at h2
  unfold nuOf
  rw [Fin.cast_eq_self]
  omega

theorem shape_odd (m₀ n : ℕ) (hm : m₀ + 1 = n) (lam : Fin (m₀ + 1) → ℤ) (hanti : Antitone lam) (ν : ℕ → ℤ) (w : ℤ)
    (hlam : ∀ i : Fin (m₀ + 1), ν (i.val + 1) = lam i + w) (hnn : ∀ i, 0 ≤ ν i) (t : Fin n) :
    nuOf (fun i => -lam i.rev) (Fin.cast hm.symm t) = (ν 1).toNat - (ν (t.rev.val + 1)).toNat := by
  subst hm
  have h1 := hlam t.rev
  have h2 := hlam 0
  have h3 : lam t.rev ≤ lam 0 := hanti (Fin.zero_le _)
  have h4 := hnn (t.rev.val + 1)
  have h5 := hnn 1
  rw [Fin.val_zero, zero_add] at h2
  unfold nuOf
  rw [Fin.cast_eq_self]
  beta_reduce
  rw [Fin.rev_last]
  omega

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem hlamS (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (l : ℕ) (hl : j + 1 ≤ l + 1) (i : Fin (X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1)) :
    X.nuv v (l + 1) s (i.val + 1) =
      liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (j + 1) i + X.Fl.w v (l + 1) s := by
  unfold liftWt
  split_ifs with h
  · exact nuv_low X l v s i.val h
  · refine nuv_high X l v s i.val h ?_
    have := i.isLt
    have h2 : (j + 1) * (X.Fl.t + 1) ≤ (l + 1) * (X.Fl.t + 1) := Nat.mul_le_mul_right _ hl
    unfold NN
    show i.val + 1 ≤ X.G.P.m + 1 + (l + 1) * (X.Fl.t + 1)
    omega

theorem not_even_of_odd {n' : ℕ} {s : Fin n'} (h : IsOddPos s) : ¬ Even s.val := by
  rw [Nat.not_even_iff]; exact h

theorem even_of_not_odd {n' : ℕ} {s : Fin n'} (h : ¬ IsOddPos s) : Even s.val :=
  Nat.even_iff.2 (by unfold IsOddPos at h; omega)

theorem c1 (j : ℕ) (b : BX X) : nuM X j b = nuS X j b := by
  funext t
  unfold nuS muX cX eX
  cases j with
  | zero =>
    show nuOf (lamAt (X.G.P.lam0 b.1) b.2) (Fin.cast (rankJ X 0).symm t) = _
    unfold lamAt
    split_ifs with h1 h2 h2
    · exact absurd h1 (not_even_of_odd h2)
    · exact shape_even _ _ (rankJ X 0) _ (X.G.P.dom b.1 b.2) (X.nuv b.1 1 b.2) _ (fun i => nuv_low X 0 b.1 b.2 i.val i.isLt)
        (nuv_nonneg X b.1 0 b.2) t
    · exact shape_odd _ _ (rankJ X 0) _ (X.G.P.dom b.1 b.2) (X.nuv b.1 1 b.2) _ (fun i => nuv_low X 0 b.1 b.2 i.val i.isLt)
        (nuv_nonneg X b.1 0 b.2) t
    · exact absurd (even_of_not_odd h2) h1
  | succ j =>
    show nuOf (lamAt ((X.Fl.Pj (j + 1)).lam0 b.1) b.2) (Fin.cast (rankJ X (j + 1)).symm t) = _
    unfold lamAt
    split_ifs with h1 h2 h2
    · exact absurd h1 (not_even_of_odd h2)
    · exact shape_even _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1 + 1) b.2) _
        (hlamS X j b.1 b.2 (j + 1) (by omega)) (nuv_nonneg X b.1 (j + 1) b.2) t
    · exact shape_odd _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1 + 1) b.2) _
        (hlamS X j b.1 b.2 (j + 1) (by omega)) (nuv_nonneg X b.1 (j + 1) b.2) t
    · exact absurd (even_of_not_odd h2) h1

theorem nuv_top (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : X.nuv v (j + 1) s (NN X.G.P.m X.t (j + 1)) = 0 := by
  apply nuv_zero X v j s
  unfold NN
  have : j * (X.t + 1) < (j + 1) * (X.t + 1) := by nlinarith
  omega

theorem c2 (j : ℕ) (b : BX X) : nuM X (j + 1) b = nuT X j b := by
  funext t
  unfold nuT muX cX
  show nuOf (lamAt ((X.Fl.Pj (j + 1)).lam0 b.1) b.2) (Fin.cast (rankJ X (j + 1)).symm t) = _
  unfold lamAt
  split_ifs with h1 h2 h2
  · exact absurd h1 (not_even_of_odd h2)
  · have := shape_even _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1) b.2) _
      (hlamS X j b.1 b.2 j le_rfl) (nuv_nonneg X b.1 j b.2) t
    rw [nuv_top X j b.1 b.2] at this
    refine this.trans ?_
    simp
  · exact shape_odd _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1) b.2) _
      (hlamS X j b.1 b.2 j le_rfl) (nuv_nonneg X b.1 j b.2) t
  · exact absurd (even_of_not_odd h2) h1

theorem nuv_anti (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) {a c : ℕ} (h : a ≤ c) :
    X.nuv v (j + 1) s (c + 1) ≤ X.nuv v (j + 1) s (a + 1) := by
  by_cases hc : c < X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1
  · rw [hlamS X j v s j le_rfl ⟨c, hc⟩, hlamS X j v s j le_rfl ⟨a, lt_of_le_of_lt h hc⟩]
    have := X.Fl.domJ (j + 1) v s (show (⟨a, lt_of_le_of_lt h hc⟩ : Fin _) ≤ ⟨c, hc⟩ from h)
    linarith
  · rw [nuv_zero X v j s (c + 1) (by
      have h1 : NN X.G.P.m X.t j ≤ NN X.G.P.m X.t (j + 1) := NN_le X j
      have h2 : NN X.G.P.m X.t (j + 1) = X.G.P.m + 1 + (j + 1) * (X.Fl.t + 1) := rfl
      omega)]
    exact nuv_nonneg X v j s _

theorem c3 (j n : ℕ) (b : BX X) : Antitone (muX X j n b) := by
  intro a c hac
  unfold muX
  exact Int.toNat_le_toNat (nuv_anti X j b.1 b.2 hac)

theorem c4 (j n : ℕ) (b : BX X) (t : Fin n) : muX X j n b t ≤ cX X j b := by
  unfold muX cX
  exact Int.toNat_le_toNat (nuv_le_first X b.1 j b.2 _)

theorem c56 (j n : ℕ) (h1 : NN X.G.P.m X.t j ≤ n) (h2 : n ≤ NN X.G.P.m X.t (j + 1)) (b : BX X) (k : ℕ) :
    colH (muX X j n b) k = X.colHt b.1 (j + 1) b.2 k := by
  unfold colH muX Sys.colHt
  rw [BidetPairing.card_fin_filter n fun t => k < (X.nuv b.1 (j + 1) b.2 (t + 1)).toNat]
  refine Finset.card_bij (fun t _ => t + 1) ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter, Finset.mem_range] at ht
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, Int.lt_toNat.1 ht.2⟩
  · intro a _ c _ h
    omega
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc] at hi
    have hin : i ≤ n := by
      by_contra hc
      have := nuv_zero X b.1 j b.2 i (by omega)
      rw [this] at hi
      have := hi.2
      omega
    refine ⟨i - 1, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [show i - 1 + 1 = i by omega]
    exact Int.lt_toNat.2 hi.2

theorem NJ_pos (j : ℕ) : 0 < NN X.G.P.m X.t j := by unfold NN; omega

theorem c7 (j : ℕ) (b : BX X) (t : Fin (NJ X j)) : eX X j b ≤ muX X j (NJ X j) b t := by
  unfold eX muX
  have h := nuv_anti X j b.1 b.2 (show t.val ≤ NJ X j - 1 by have := t.isLt; omega)
  have hN : NJ X j - 1 + 1 = NJ X j := Nat.sub_add_cancel (NJ_pos X j)
  rw [hN] at h
  exact Int.toNat_le_toNat h

theorem c8 (j : ℕ) (b : BX X) (t : Fin (NJ X j)) (ht : t.val + 1 = NJ X j) : muX X j (NJ X j) b t = eX X j b := by
  unfold eX muX
  rw [ht]

theorem eJ_odd (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (h : IsOddPos s) : eJ X j v s = -X.G.P.lam0 v s 0 := by
  have h1 := numO X j v s h
  have h2 : cMu X j v s = X.G.P.lam0 v s ⟨0, by omega⟩ + X.Fl.w v (j + 1) s := nuv_low X j v s 0 (by omega)
  have h3 : X.w v (j + 1) s = X.Fl.w v (j + 1) s := rfl
  have h4 : (⟨0, by omega⟩ : Fin (X.G.P.m + 1)) = 0 := rfl
  rw [h4] at h2
  linarith

theorem c9 (j : ℕ) (b : BX X) (h : ¬ IsOddPos b.2) :
    (eX X j b : ℤ) = eJ X j b.1 b.2 + X.w b.1 (j + 1) b.2 ∧ eJ X (j + 1) b.1 b.2 = -X.w b.1 (j + 1) b.2 := by
  obtain ⟨h1, h2⟩ := numE X j b.1 b.2 h
  refine ⟨?_, ?_⟩
  · unfold eX
    rw [Int.toNat_of_nonneg h1, h2]
  · have h3 := hlamS X j b.1 b.2 j le_rfl (Fin.last _)
    have h4 : X.nuv b.1 (j + 1) b.2 ((Fin.last (X.G.P.m + (j + 1) * (X.Fl.t + 1))).val + 1) = 0 := by
      have := nuv_top X j b.1 b.2
      rw [Fin.val_last]
      have e : X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1 = NN X.G.P.m X.t (j + 1) := by
        show _ = X.G.P.m + 1 + (j + 1) * (X.Fl.t + 1)
        omega
      rw [e]; exact this
    rw [h4] at h3
    have h5 : eJ X (j + 1) b.1 b.2 =
        liftWt X.Fl.t X.G.P.m (X.G.P.lam0 b.1 b.2) (fun i => X.Fl.w b.1 i b.2) (j + 1) (Fin.last _) := by
      show lamAt _ b.2 _ = _
      unfold lamAt
      rw [if_pos (even_of_not_odd h)]
      rfl
    rw [h5]
    have h6 : X.w b.1 (j + 1) b.2 = X.Fl.w b.1 (j + 1) b.2 := rfl
    linarith

theorem c10 (j : ℕ) (b : BX X) (h : IsOddPos b.2) :
    (cX X j b : ℤ) = X.w b.1 (j + 1) b.2 - eJ X j b.1 b.2 ∧ eJ X (j + 1) b.1 b.2 = eJ X j b.1 b.2 := by
  refine ⟨?_, by rw [eJ_odd X (j + 1) b.1 b.2 h, eJ_odd X j b.1 b.2 h]⟩
  have h1 := numO X j b.1 b.2 h
  rw [← h1]
  exact cMu_toNat X b.1 j b.2

end FrameShapeLemmas

open FrameShapeLemmas in
theorem frame_shape_identity_holds : XShape := by
  intro p _ X j b
  exact ⟨c1 X j b, c2 X j b, fun n => c3 X j n b, fun n t => c4 X j n b t, c56 X j _ le_rfl (NN_le X j) b,
    c56 X j _ (NN_le X j) le_rfl b, c7 X j b, c8 X j b, c9 X j b, c10 X j b⟩

end Formalism.L2.PairingIndexBounds.Ent
end
end

