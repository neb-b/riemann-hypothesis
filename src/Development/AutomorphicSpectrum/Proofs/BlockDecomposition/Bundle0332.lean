module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0246
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0312
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0313
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0317
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMulSqLe
section
open MeasureTheory
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.DualVectorFamily

theorem sum_mul_sq_le {κ : Type} (s : Finset κ) (p q : κ → ℝ≥0∞) (t : ℝ≥0∞) (h : ∀ l ∈ s, q l ^ 2 ≤ t) :
    (∑ l ∈ s, p l * q l) ^ 2 ≤ (∑ l ∈ s, p l) ^ 2 * t := by
  have hs : (t ^ (1 / 2 : ℝ)) ^ 2 = t := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hq : ∀ l ∈ s, q l ≤ t ^ (1 / 2 : ℝ) := by
    intro l hl
    have := h l hl
    rw [← hs] at this
    exact (ENNReal.pow_le_pow_left_iff (by norm_num)).1 this
  calc (∑ l ∈ s, p l * q l) ^ 2 ≤ ((∑ l ∈ s, p l) * t ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun l hl => by gcongr; exact hq l hl
    _ = (∑ l ∈ s, p l) ^ 2 * t := by rw [mul_pow, hs]

theorem abs_vecs (hKB : KerBasic) (hKL : KerLin) (hCB : CntBasic) (hVE : VecEx) (hVN : VecNorm)
    (hVI : VecInner) (hPt : PtEq) (X : Ctx) (th : X.G → X.G) (hth : Continuous th)
    (hcnt : ∀ (Ω : Set X.G) x, cnt X.Γ Ω (th x) = cnt X.Γ (th '' Ω) x)
    {ι : Type} [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (X.G → ℂ)) (T₁ T₂ : X.Hs ι →L[ℂ] X.Hs ι)
    (M : Matrix ι ι ℂ) (t₁ : ∀ i j, Tst (Φ₁ i j)) (t₂ : ∀ i j, Tst (Φ₂ i j))
    (o₁ : X.IsOp Φ₁ T₁) (o₂ : X.IsOp Φ₂ T₂) :
    ∃ k₁ k₂ : X.G → ι → X.Hs ι,
      (∀ i, Continuous (fun x => k₁ x i) ∧ Continuous fun x => k₂ x i) ∧
      (∀ x i (u : X.Hs ι), inner ℂ (k₁ x i) u = ∑ j, ∫ y, ker X.Γ (Φ₁ i j) x y * (u j : X.G → ℂ) y ∂X.ν) ∧
      (∀ x i (u : X.Hs ι), inner ℂ u (k₂ x i) =
        ∑ j, ∑ l, ∫ y, starRingEnd ℂ ((u j : X.G → ℂ) y) * ker X.Γ (Φ₂ j l) y (th x) * M l i ∂X.ν) ∧
      (∃ (C : ℝ≥0∞) (Ω : Set X.G), C ≠ ⊤ ∧ IsCompact Ω ∧ ∀ x i,
        ‖k₁ x i‖ₑ ^ 2 ≤ C * cnt X.Γ Ω x ∧ ‖k₂ x i‖ₑ ^ 2 ≤ C * cnt X.Γ Ω x) ∧
      (∀ (U : X.Hs ι →L[ℂ] X.Hs ι) (Φ : Matrix ι ι (X.G → ℂ)), (∀ i j, Tst (Φ i j)) →
        X.IsOp Φ (T₁ * U * T₂) → ∀ x,
          ker X.Γ (fun y => ∑ i, ∑ j, Φ i j y * M j i) x (th x) =
            ∑ i, inner ℂ (k₁ x i) (U (k₂ x i))) := by
  have tA : ∀ i j, Tst ((fun i j => adj (Φ₁ j i) : Matrix ι ι (X.G → ℂ)) i j) :=
    fun i j => (hKB X _ (t₁ j i)).2.2.2.1
  obtain ⟨k₁, c₁, v₁⟩ := hVE X ι (fun i j => adj (Φ₁ j i)) tA
  obtain ⟨k, c, v⟩ := hVE X ι Φ₂ t₂
  obtain ⟨C₁, Ω₁, C₁t, Ω₁c, n₁⟩ := hVN X ι (fun i j => adj (Φ₁ j i)) tA
  obtain ⟨C₂, Ω₂, C₂t, Ω₂c, n₂⟩ := hVN X ι Φ₂ t₂
  refine ⟨k₁, fun x i => ∑ l, M l i • k (th x) l, fun i => ⟨c₁ i, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact continuous_finsetSum _ fun l _ => ((c l).comp hth).const_smul (M l i)
  · intro x i u
    exact (hVI X ι Φ₁ x i (k₁ x i) u t₁).2 (v₁ x i)
  · intro x i u
    rw [inner_sum]
    simp only [inner_smul_right, (hVI X ι Φ₂ (th x) _ (k (th x) _) u t₂).1 (v _ _), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const, mul_comm]
  · set P : ℝ≥0∞ := ∑ i, (∑ l, ‖M l i‖ₑ) ^ 2 with hP
    have Pt : P ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ =>
      ENNReal.pow_ne_top (ENNReal.sum_ne_top.2 fun l _ => eNorm_ne_top)
    refine ⟨C₁ + P * C₂, Ω₁ ∪ th '' Ω₂, ENNReal.add_ne_top.2 ⟨C₁t, ENNReal.mul_ne_top Pt C₂t⟩,
      Ω₁c.union (Ω₂c.image hth), fun x i => ⟨?_, ?_⟩⟩
    · calc ‖k₁ x i‖ₑ ^ 2 ≤ C₁ * cnt X.Γ Ω₁ x := n₁ x i _ (v₁ x i)
        _ ≤ (C₁ + P * C₂) * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by
          gcongr
          · exact le_self_add
          · exact (hCB X).2.2.1 _ _ Set.subset_union_left x
    · have hb : ∀ l ∈ (Finset.univ : Finset ι), ‖k (th x) l‖ₑ ^ 2 ≤ C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by
        intro l _
        calc ‖k (th x) l‖ₑ ^ 2 ≤ C₂ * cnt X.Γ Ω₂ (th x) := n₂ _ l _ (v _ l)
          _ = C₂ * cnt X.Γ (th '' Ω₂) x := by rw [hcnt]
          _ ≤ _ := by
            gcongr
            exact (hCB X).2.2.1 _ _ Set.subset_union_right x
      have hsum : ‖∑ l, M l i • k (th x) l‖ₑ ≤ ∑ l, ‖M l i‖ₑ * ‖k (th x) l‖ₑ := by
        refine (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [eNorm_smul]
      calc ‖∑ l, M l i • k (th x) l‖ₑ ^ 2 ≤ (∑ l, ‖M l i‖ₑ * ‖k (th x) l‖ₑ) ^ 2 := by gcongr
        _ ≤ (∑ l, ‖M l i‖ₑ) ^ 2 * (C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x) := sum_mul_sq_le _ _ _ _ hb
        _ ≤ P * (C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x) := by
          gcongr
          exact Finset.single_le_sum (f := fun i => (∑ l, ‖M l i‖ₑ) ^ 2) (fun _ _ => zero_le) (Finset.mem_univ i)
        _ = P * C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by rw [mul_assoc]
        _ ≤ (C₁ + P * C₂) * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by
          gcongr
          exact le_add_self
  · intro U Φ tΦ oΦ x
    have hfun : (fun y => ∑ i, ∑ j, Φ i j y * M j i) =
        fun y => ∑ p : ι × ι, Φ p.1 p.2 y * M p.2 p.1 := by
      funext y
      rw [Fintype.sum_prod_type]
    rw [hfun, (hKL X (ι × ι) (fun p => Φ p.1 p.2) (fun p => M p.2 p.1) fun p => tΦ _ _).2,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, inner_smul_right,
      hPt X ι Φ₁ Φ₂ Φ T₁ T₂ U t₁ t₂ tΦ o₁ o₂ oΦ x (th x) i l (k₁ x i) (k (th x) l) (v₁ x i) (v _ l),
      mul_comm]

theorem vecsEx_of : RatProper → KerBasic → KerLin → CntBasic → CntPair → VecEx → VecNorm → VecInner → PtEq →
    VecsEx := by
  intro hR hKB hKL hCB hCP hVE hVN hVI hPt E _ _ _ a b D ι _ Φ₁ Φ₂ T₁ T₂ M h₁ h₂ o₁ o₂
  open PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep in
  letI : MeasurableSpace (H E a b) := borelH E a b
  let X : Ctx := by
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E b
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E b
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E b
    haveI := (hR E a).2.1
    haveI := (hR E b).2.1
    haveI := D.haar.1
    haveI := D.haar.2.2.1
    haveI : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
    haveI : IsFiniteMeasureOnCompacts D.μ := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    exact { G := H E a b
            ms := borelH E a b
            bs := ⟨rfl⟩
            μ := D.μ
            haar := ⟨⟩
            Γ := ratH E a b
            cn := (((ratGL E a).prodMap (ratGL E b)).rangeRestrict_surjective).countable
            proper := by
              intro C hC
              have h1 := (hR E a).2.2 _ (hC.image continuous_fst)
              have h2 := (hR E b).2.2 _ (hC.image continuous_snd)
              refine ((h1.prod h2).image ((ratGL E a).prodMap (ratGL E b)).rangeRestrict).subset ?_
              rintro ⟨_, γ, rfl⟩ hγ
              exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩
            F := D.F
            fd := D.fd }
  obtain ⟨k₁, k₂, c, r₁, r₂, n, d⟩ := abs_vecs hKB hKL hCB hVE hVN hVI hPt X th
    (hCP E a b).2.1 (hCP E a b).1 Φ₁ Φ₂ T₁ T₂ M h₁ h₂ o₁ o₂
  refine ⟨k₁, k₂, ⟨c, r₁, r₂, n, ?_⟩⟩
  intro U Φ hΦ hop x
  rw [(hCP E a b).2.2]
  exact d U Φ hΦ hop x

end GlobalTheory.CompanionTheory.DualVectorFamily

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopGradedRepOpenCompat
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.LExact

open GlobalTheory.CompanionTheory.CupRep

section
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ) (V : X.Opens)
  {d : ℕ} (t : Fin d → Γ(X, V)) (E : Frame (sP (KS q s {V})) d)
  (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D) (σ : ∀ T, E.D ⟶ T)

def lf (g : Γ(X, V)) (T : (KS q s {V}).FullSubcategory) : (sP (KS q s {V})).A.obj T :=
  liftV T.obj (ks_in q s V T.obj T.property) g

variable {q s V t E ε}

theorem lf_sub_mem (hL : IsLoc q s t E ε) (g : Γ(X, V)) (T : (KS q s {V}).FullSubcategory) (u : E.D ⟶ T) :
    lf q s V g T - ((sP (KS q s {V})).A.map u).hom (ε g) ∈ (sP (KS q s {V})).J.S T := by
  have a1 : Ideal.Quotient.mk T.obj.J (lf q s V g T) = ev T.obj (ks_in q s V T.obj T.property) g :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective (ev T.obj (ks_in q s V T.obj T.property) g))
  have a2 := hL.2.2.2.1 T u g
  exact Ideal.Quotient.eq.1 (a1.trans a2)

theorem addC_eq (hL : IsLoc q s t E ε) (k : Fin d) (u : ComposableArrows (KS q s {V}).FullSubcategory 1) :
    (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from addC (KS q s {V}) (lf q s V (t k)) u) -
      (∑ i, E.form σ ![i] (if k = i then 1 else 0) u +
        ((lf q s V (t k) (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k))) -
          ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom
            (lf q s V (t k) (u.obj 0) - ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k))))) = 0 := by
  have e1 : ∑ i, E.form σ ![i] (if k = i then (1 : (sP (KS q s {V})).A.obj E.D) else 0) u =
      E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) := by
    simp only [DlogApprox.form_one]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, map_one, mul_one]
    · intro b _ hb
      rw [if_neg (Ne.symm hb), map_zero, mul_zero]
    · simp
  have e2 : E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) =
      ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k)) -
      ((sP (KS q s {V})).A.map (σ _ ≫ u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (ε (t k)) :=
    hL.2.2.2.2 k _ _
  have e3 : ((sP (KS q s {V})).A.map (σ _ ≫ u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (ε (t k)) =
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (((sP (KS q s {V})).A.map (σ _)).hom (ε (t k))) := by
    rw [Functor.map_comp]; rfl
  rw [e1, e2, e3, map_sub]
  change (lf q s V (t k) (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (lf q s V (t k) (u.obj 0))) - _ = 0
  abel
end

section
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}
  (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)

theorem fc_zero {j : ℕ} (I : Fin j → Fin d) : fc E σ I 0 = 0 := by
  funext s
  change E.form σ I 0 s = 0
  unfold Frame.form
  rw [map_zero, mul_zero]

theorem sum_fc_delta (m : ℕ) (E : Frame Φ m) (σ : ∀ T : C, E.D ⟶ T) :
    ∑ I : Fin m → Fin m, fc E σ I (∏ k, if k = I k then (1 : Φ.A.obj E.D) else 0) = fc E σ id 1 := by
  rw [Finset.sum_eq_single id]
  · simp
  · intro I _ hI
    obtain ⟨k, hk⟩ : ∃ k, k ≠ I k := by
      by_contra hh
      push_neg at hh
      exact hI (funext fun k => (hh k).symm)
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk), fc_zero]
  · simp
end

section
variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {s : ℕ} {V : X.Opens}

theorem rep_xdt {n : ℕ} {t : Fin (n + 1) → Γ(X, V)} {E : Frame (sP (KS q s {V})) (n + 1)}
    {ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D} (hL : IsLoc q s t E ε) (σ : ∀ T, E.D ⟶ T) (w : Γ(X, V))
    (r : ℤ) (hr : r = ((n + 1 : ℕ) : ℤ)) (cl : HQ (KS q s {V}) r (r + 1) (n + 1))
    (h : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (E.form σ id (ε w)) cl) :
    CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (xdtC s V t w) cl := by
  subst hr
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  have hc : E.GrConst (sFil (KS q s {V})) := hL.1
  let ℓ : Fin (n + 1) → CH.Cn (CH.modF (sP (KS q s {V})).A) 1 := fun k => addC (KS q s {V}) (lf q s V (t k))
  let cc : Fin (n + 1) → Fin (n + 1) → (sP (KS q s {V})).A.obj E.D := fun k i => if k = i then 1 else 0
  let hh : Fin (n + 1) → ∀ T, (sP (KS q s {V})).A.obj T := fun k T =>
    lf q s V (t k) T - ((sP (KS q s {V})).A.map (σ T)).hom (ε (t k))
  have hJ : ∀ k T, hh k T ∈ (sP (KS q s {V})).J.S T := fun k T => lf_sub_mem hL _ T (σ T)
  have hh0 : ∀ k, h0 (hh k) ∈ FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 0 := fun k => mem_FC.2 fun u => by
    have := hJ k (u.obj (Fin.last 0))
    rw [← hF.one] at this
    rw [Nat.cast_one]
    exact this
  have he : ∀ k, ℓ k - (∑ i, fc E σ ![i] (cc k i) + CH.d (CH.modF (sP (KS q s {V})).A) 0 (h0 (hh k))) ∈
      FC (sFil (KS q s {V}) ((1 + 1 : ℕ) : ℤ)) 1 := fun k => mem_FC.2 fun u => by
    have e : vl (ℓ k - (∑ i, fc E σ ![i] (cc k i) + CH.d (CH.modF (sP (KS q s {V})).A) 0 (h0 (hh k)))) u =
        (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from ℓ k u) - (∑ i, E.form σ ![i] (cc k i) u +
          (hh k (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (hh k (u.obj 0)))) := by
      rw [← cech_d_h0_eval]
      change _ - (vl (∑ i, fc E σ ![i] (cc k i)) u + _) = _
      congr 2
      rw [vl, Finset.sum_apply]
      rfl
    rw [e]
    have e0 := addC_eq σ hL k u
    exact e0 ▸ Ideal.zero_mem _
  obtain ⟨g, hg, hn⟩ := near E σ hF hc (n + 1) ℓ cc (fun k => h0 (hh k)) hh0 he
  obtain ⟨H, hH, rfl⟩ := hg
  rw [show (∑ I : Fin (n + 1) → Fin (n + 1), fc E σ I (∏ k, cc k (I k))) = fc E σ id 1 from sum_fc_delta _ E σ] at hn
  have hcL : cupListC (sP (KS q s {V})).A ℓ ∈ FC (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)) (n + 1) := by
    have h1 := FC_anti hF (r := ((n + 1 : ℕ) : ℤ)) (by push_cast; omega) hn
    have h2 : fc E σ id (1 : (sP (KS q s {V})).A.obj E.D) ∈ FC (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)) (n + 1) := fc_mem E σ hF id 1
    have h3 := d_mem hH
    have := add_mem (add_mem h1 h3) h2
    rwa [sub_add_cancel, sub_add_cancel] at this
  let H' : CH.Cn (CH.modF (sP (KS q s {V})).A) n := fun u => (show (sP (KS q s {V})).A.obj (u.obj (Fin.last n)) from H u) * ((sP (KS q s {V})).A.map (σ _)).hom (ε w)
  have hH' : H' ∈ FC (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)) n :=
    mem_FC.2 fun u => Ideal.mul_mem_right _ _ (mem_FC.1 hH u)
  have h1 := rep_add h (rep_d (b := sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)) H' (mem_FC.1 hH'))
  rw [add_zero] at h1
  refine rep_congr h1 fun u => ?_
  have e1 := mem_FC.1 hn u
  have e2 := d_mul E σ hF hc (ε w) hH u
  have e5 := form_mul E σ id (ε w) 1 u
  rw [mul_one] at e5
  let ψ := u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))))
  let T0 := u.obj (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))
  have a1 : ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0 - ((sP (KS q s {V})).A.map (σ T0)).hom (ε w)) ∈
      (sP (KS q s {V})).J.S _ := (sP (KS q s {V})).J.map_mem ψ (lf_sub_mem hL w T0 (σ T0))
  have a2 := DlogApprox.const1 hF hc (σ T0 ≫ ψ) (σ (u.obj (Fin.last (n + 1)))) (ε w)
  have a3 : ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0) - ((sP (KS q s {V})).A.map (σ (u.obj (Fin.last (n + 1))))).hom (ε w) ∈
      (sFil (KS q s {V}) ((1 : ℕ) : ℤ)).S _ := by
    rw [Nat.cast_one, hF.one]
    have a4 := ((sP (KS q s {V})).J.S _).add_mem a1 a2
    have e3 : ((sP (KS q s {V})).A.map (σ T0 ≫ ψ)).hom (ε w) =
        ((sP (KS q s {V})).A.map ψ).hom (((sP (KS q s {V})).A.map (σ T0)).hom (ε w)) := by
      rw [Functor.map_comp]; rfl
    rw [e3, map_sub, sub_add_sub_cancel] at a4
    exact a4
  have ex : vl (xdtC (q := q) s V t w) u = ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0) * vl (cupListC (sP (KS q s {V})).A ℓ) u :=
    congrArg (fun b : (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) => ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0) * b)
      (CrystallineSemistableComparison.Auxff.term_id _ u _ _ _ (fun t => by simp [CH.back]))
  have e6 := hF.mul 1 (n + 1) _ a3 (mem_FC.1 hcL u)
  have e7 : ((1 + (n + 1) : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  have e8 : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [e7] at e6
  rw [e8] at e1 e2
  have e9 := ((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).add_mem
    (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).add_mem
      (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).neg_mem
        (Ideal.mul_mem_right (((sP (KS q s {V})).A.map (σ (u.obj (Fin.last (n + 1))))).hom (ε w)) _ e1))
      (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).neg_mem e2))
    (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).neg_mem e6)
  change E.form σ id (ε w) u + vl (CH.d (CH.modF (sP (KS q s {V})).A) n H') u - vl (xdtC (q := q) s V t w) u ∈ _
  rw [ex, e5]
  convert e9 using 1
  change _ = -((vl (cupListC (sP (KS q s {V})).A ℓ) u - vl (fc E σ id 1) u - vl (CH.d (CH.modF (sP (KS q s {V})).A) n H) u) * _) +
    -(vl (CH.d (CH.modF (sP (KS q s {V})).A) n H) u * _ - vl (CH.d (CH.modF (sP (KS q s {V})).A) n H') u) + -(_ * _)
  ring
end

theorem main : CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → CrystallineSemistableComparison.Pb.KH.GrAff →
    ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) q] (s : ℕ), n + 1 < s → ∀ (V V' : X.Opens) (hVV : V ≤ V'), IsAffineOpen V' →
    ∀ (c : Coord q V (n + 1)),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin (n + 1) → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (f : CH.Cn (CH.modF (sP (KS q s {V'})).A) n), (∀ σ, f σ ∈ (sFil (KS q s {V'}) n).S _) →
      (∀ σ, CH.d _ n f σ ∈ (sFil (KS q s {V'}) ((n : ℤ) + 1)).S _) →
      ∀ x : HQ (KS q s {V'}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1), Rep (sFil (KS q s {V'}) ((n : ℤ) + 1)) (sFil (KS q s {V'}) ((n : ℤ) + 1 + 1)) (CH.d _ n f) (x) →
      ∃ η : Fin (n + 1) → Γ(X, V), (∀ k, η k ∈ jacSpan hVV (RingHom.id _) (fun k => D k) (Fin.succAbove k)) ∧
        Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V c.t (∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (η k))) (resKS q s hVV _ _ _ x) := by
  intro _ _ _ K _ _ X q n _ s hs V V' hVV hV' c D hD f hf hdf x hx
  haveI : Smooth q := SmoothOfRelativeDimension.smooth (n + 1) q
  obtain ⟨E, ε, hL⟩ := _root_.GlobalTheory.CompanionTheory.ConeLocal.exists_loc q c s (by omega)
  let σ : ∀ T, E.D ⟶ T := fun T => (E.ne T).some
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  have hc : E.GrConst (sFil (KS q s {V})) := hL.1
  have hT := GlobalTheory.T.taylor_of_local_frame q c s E ε hL D hD
  have hr : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨ξ, hξ⟩ := rep_exists (a := sFil (KS q s {V'}) (n : ℤ)) (b := sFil (KS q s {V'}) ((n : ℤ) + 1)) f hf hdf
  have h1 := rep_res (ks_le q s hVV) _ _ hξ
  have h2 := rep_res (ks_le q s hVV) _ _ hx
  obtain ⟨y, hy⟩ := (_root_.GlobalTheory.CompanionTheory.ConeLocal.loc_coef q c.t s E ε hL σ n (n : ℤ) rfl (by omega)).1 (resKS q s hVV _ _ _ ξ)
  have hmem := GlobalTheory.T.local_frame_derivation_compat q s hVV hV' c D hD E ε hL σ n (n : ℤ) rfl (by omega) ξ y hy
  have h2' : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1))
      (fun u => CH.d _ n (resQ (ks_le q s hVV) f) u) (resKS q s hVV _ _ _ x) := by
    refine rep_congr h2 fun u => ?_
    have e := congrFun (d_resQ (ks_le q s hVV) f) u
    exact (sub_eq_zero.2 e.symm) ▸ Ideal.zero_mem _
  have h3 := GlobalTheory.T.taylor_differential_representative hF E σ hc _ hT n (resQ (ks_le q s hVV) f) (fun I => ε (y I)) (resKS q s hVV _ _ _ ξ) (resKS q s hVV _ _ _ x) h1 hy h2'
  have h4 := _root_.GlobalTheory.CompanionTheory.ConeLocal.rep_collapse hF E σ hc (n + 1) _ hr (fun a : Idx n (n + 1) × Fin (n + 1) => Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2)
    (fun a => (-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1))))) _ h3
  have h5 := rep_one E σ _ (fun I => ∑ a : Idx n (n + 1) × Fin (n + 1), sgn I (Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2) • ((-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1)))))) _ h4
  let Ik : Fin (n + 1) → Idx n (n + 1) := fun k => ⟨k.succAbove, Fin.strictMono_succAbove k⟩
  let sg : Fin (n + 1) → ℤ := fun k => sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) (Ik k).1 k)
  refine ⟨fun k => ((-1 : ℤ) ^ (k : ℕ) * (-1) ^ n * sg k) • y (Ik k), fun k => ?_, ?_⟩
  · exact AddSubgroup.zsmul_mem _ (hmem (Ik k)) _
  · have e : ∑ a : Idx n (n + 1) × Fin (n + 1), sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2) • ((-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1))))) =
        ε (∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (((-1 : ℤ) ^ (k : ℕ) * (-1) ^ n * sg k) • y (Ik k))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Fintype.sum_prod_type_right, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single (Ik k)]
      · have a1 : ((-1 : Γ(X, V)) ^ (k : ℕ)) * (-1) ^ (k : ℕ) = 1 := by rw [← mul_pow]; simp
        rw [map_zsmul, zsmul_eq_mul, zsmul_eq_mul, RingEquiv.symm_apply_apply]
        push_cast
        have a2 : (-1 : Γ(X, V)) ^ (k : ℕ) * (((-1) ^ (k : ℕ) * (-1) ^ n * (sg k : Γ(X, V))) * D k (y (Ik k))) =
            (sg k : Γ(X, V)) * ((-1) ^ n * D k (y (Ik k))) := by
          linear_combination ((-1) ^ n * (sg k : Γ(X, V)) * D k (y (Ik k))) * a1
        rw [a2, map_mul, map_mul, map_pow, map_neg, map_one, map_intCast]
      · intro I _ hI
        rw [sgn_snoc I k (fun h => hI (Subtype.ext h)), zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [e] at h5
    exact rep_xdt hL σ _ _ hr _ h5

end GlobalTheory.CompanionTheory.ConeLocal.LExact
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformGenerationOfVanishing
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem uniformGen_of_gradedNoeth : GradedNoeth → UniformVanishing → UniformGen := by
  intro hN hV A _ _ X _ _ H hH k M T d hM
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := hH.compactSpace
  have hcoh := _root_.GlobalTheory.CompanionTheory.GE.isCoherent_kerSeq hM
  obtain ⟨d', hd'⟩ := _root_.GlobalTheory.CompanionTheory.GE.Uniform.span_range_eq_top_uniform (KerSeq.kerOp T hM.comm d) (fun e => (hcoh e).1)
    (_root_.GlobalTheory.CompanionTheory.GE.KerSeq.kerSeq_gen_bounded hN hM)
  have hK : OpSeq k (KerSeq.kerSeq T d) (KerSeq.kerOp T hM.comm d) d' :=
    ⟨hcoh, KerSeq.kerOp_comm T hM.comm d, hd'⟩
  obtain ⟨n₀, hn₀⟩ := hV (A := A) H hH k _ _ d' hK
  refine ⟨n₀, fun n hn e he => ?_⟩
  obtain ⟨e₀, rfl⟩ := Nat.exists_eq_add_of_le he
  haveI := GlobalTheory.T.operator_sequence_sum_epi hM e₀
  exact _root_.GlobalTheory.CompanionTheory.GE.span_range_twist_eq_top (GlobalTheory.lbZPow H n) (GlobalTheory.Twist.isLB_lbZPow hH.isLB n) (fun i => T i (d + e₀))
    (kernel.ι _) (kernel.condition _) (KerSeq.kerSC_shortExact T d e₀) (hn₀ n hn e₀ 1 one_pos)

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProduct
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Leib

theorem nontrivial_piTensorProduct_iff {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] :
    Nontrivial (⨂[ℂ] i, M i) ↔ ∀ i, Nontrivial (M i) := by
  classical
  constructor
  · intro hN i
    by_contra hi
    rw [not_nontrivial_iff_subsingleton] at hi
    have h0 : ∀ x : ⨂[ℂ] i, M i, x = 0 := by
      intro x
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        rw [(PiTensorProduct.tprod ℂ).map_coord_zero i (Subsingleton.elim (f i) 0), smul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    obtain ⟨x, y, hxy⟩ := hN.exists_pair_ne
    exact hxy ((h0 x).trans (h0 y).symm)
  · intro hM
    have hv : ∀ i, ∃ v : M i, v ≠ 0 := fun i => @exists_ne _ (hM i) 0
    choose v hv using hv
    have hφ : ∀ i, ∃ φ : Module.Dual ℂ (M i), φ (v i) ≠ 0 := fun i => by
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact hv i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).1 hc)
    choose φ hφ using hφ
    refine ⟨⟨PiTensorProduct.tprod ℂ v, 0, fun h => ?_⟩⟩
    have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)) h
    simp only [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply] at h1
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hφ i) h1

theorem genericProdIff_of_whitHeredity (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : WhitHeredity k → GenericProdIff k := by
  intro hW h N d hd X _ _ π hsm
  obtain ⟨ψ, hψc, hψ1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one (k := k)
  obtain ⟨e⟩ := hW ψ hψc hψ1 h N d hd X π hsm
  simp only [GlobalTheory.LocGL.isGeneric_iff_isGenericFor hψc hψ1, GlobalTheory.LocGL.IsGenericFor]
  exact Iff.trans ⟨fun hn => @Equiv.nontrivial _ _ e.symm.toEquiv hn, fun hn => @Equiv.nontrivial _ _ e.toEquiv hn⟩
    (nontrivial_piTensorProduct_iff _)

end GlobalTheory.CompanionTheory.Leib

end
end

