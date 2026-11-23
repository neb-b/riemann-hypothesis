module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeSpan
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntertwinerUnipotentInvariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0590
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0581
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SepOfHausdorff
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WachTensor

noncomputable section

namespace GlobalTheory.NL.BaseField

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l}

theorem res_eq_one_iff (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (g : ↥(GK K)) : W.resΓ g = 1 ↔ P.χQ (g : GQ l) = 1 := by
  have h1 := W.χΓ_res g
  rw [P.PD_χ] at h1
  constructor
  · intro h
    rw [h, map_one, Units.val_one, map_one] at h1
    exact Units.ext ((algebraMap ℚ_[l] ↥LL.1).injective (h1.symm.trans (map_one _).symm))
  · intro h
    rw [h, Units.val_one, map_one] at h1
    apply W.χΓ_inj
    rw [map_one]
    exact Units.ext (Subtype.ext h1)

theorem ker_transfer {K' : FinExt l}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (W' : LocWach (P.PD K') ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K')))
    (h : Good K s LL) (h0 : K0 K = K0 K') (g' : ↥(GK K')) (hg : W'.resΓ g' = 1) :
    ∃ g : ↥(GK K), W.resΓ g = 1 ∧ (g : GQ l) = g' :=
  have h1 := (res_eq_one_iff W' g').1 hg
  ⟨⟨g', mem_GK_of_chi P h.2.2.1 h0 g'.2 h1⟩, (res_eq_one_iff W _).2 h1, rfl⟩

theorem sep_of_hausdorff {R : Type} [CommRing R] (a : R) (h : IsHausdorff (Ideal.span {a}) R) (x : R)
    (hx : ∀ k : ℕ, a ^ k ∣ x) : x = 0 :=
  h.haus x fun k => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx k

end Concrete


set_option maxHeartbeats 1600000 in
theorem rings_mem (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (h0 : K0 K = K0 K') :
    (∀ a, ∃ a', ((F l).E K' s LL h').tie.io a' = ((F l).E K s LL h).tie.io a) ∧
      ∀ a, ∃ a', ((F l).E K' s LL h').tie.ioE a' = ((F l).E K s LL h).tie.ioE a := by
  obtain ⟨c1, -, c3, -, c5⟩ := GlobalTheory.HWL.TensorWitt.main l LL
  have h1 : ∀ a, ∃ a', ((F l).E K' s LL h').tie.io a' = ((F l).E K s LL h).tie.io a :=
    io_mem _ _ Subtype.val_injective (descends _) c3 (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').2.2.2.2.2.1
      (fun g' hg' => by
        obtain ⟨g, hg, e⟩ := ker_transfer _ _ h h0 g' hg'
        exact ⟨g, hg, congrArg ((D.locA l).gRW LL) e⟩)
      (sep_of_hausdorff _ (c5 _ (GlobalTheory.Cyc.εroot_sub_one_not_unit (D.locA l) s)).toIsHausdorff)
  refine ⟨h1, ioE_mem _ _ (((D.loc l).PD_p K').trans ((D.loc l).PD_p K).symm) h1 ?_⟩
  rw [(D.loc l).PD_p K]
  exact sep_of_hausdorff _ c1.toIsHausdorff

section Two

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K K' : FinExt l} {s : ℕ} {LL : FinExt l}
  {h : Good K s LL} {h' : Good K' s LL}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
  {W' : LocWach (P.PD K') ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K'))}
  (E : EtSit P AI K s LL h W) (E' : EtSit P AI K' s LL h' W') (T : Lt K LL) (T' : Lt K' LL)


set_option maxHeartbeats 800000 in
theorem jD_mem_sit (h0 : K0 K = K0 K') (hE : ∀ x, ∃ x', E'.tie.ioE x' = E.tie.ioE x)
    (e : ↥T.L.T →ₗ[↥(OL LL)] ↥T'.L.T)
    (he : ∀ (g : ↥(GK K)) (g' : ↥(GK K')), (g : GQ l) = g' → ∀ t, e (T.actT g t) = T'.actT g' (e t))
    (x : W.DD T) : ∃ x', E'.tie.jD T' x' =
      TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) e (E.tie.jD T x) :=
  jD_mem E.tie E'.tie (descends E') (map_ne_top E) (φRW_surjective LL) hE T T' e (fun g' hg' =>
    (ker_transfer W W' h h0 g' hg').imp fun g hg => ⟨hg.1, congrArg (AI.gRW LL) hg.2, he g g' hg.2⟩) x

variable (hle : K.1 ≤ K'.1) (eT : ↥T'.L.T ≃ₗ[↥(OL LL)] ↥T.L.T)
  (hact : ∀ (g : ↥(GK K')) (t : ↥T'.L.T), eT (T'.actT g t) = T.actT ⟨(g : GQ l), GK_le hle g.2⟩ (eT t))

include hact in
theorem act_fwd (g' : ↥(GK K')) (g : ↥(GK K)) (e : (g' : GQ l) = g) (t : ↥T'.L.T) :
    eT.toLinearMap (T'.actT g' t) = T.actT g (eT.toLinearMap t) :=
  (hact g' t).trans (congrArg (fun u : ↥(GK K) => T.actT u (eT t)) (Subtype.ext e))

include hact in
theorem act_bwd (g : ↥(GK K)) (g' : ↥(GK K')) (e : (g : GQ l) = g') (t : ↥T.L.T) :
    eT.symm.toLinearMap (T.actT g t) = T'.actT g' (eT.symm.toLinearMap t) := by
  apply eT.injective
  have h1 := act_fwd T T' hle eT hact g' g e.symm (eT.symm t)
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1 ⊢
  exact h1.symm

set_option maxHeartbeats 800000 in
include hact in
theorem jD_bwd (h0 : K0 K = K0 K') (hE : ∀ x, ∃ x', E'.tie.ioE x' = E.tie.ioE x) (x : W.DD T) :
    ∃ x', TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap
      (E'.tie.jD T' x') = E.tie.jD T x :=
  (jD_mem_sit E E' T T' h0 hE eT.symm.toLinearMap (act_bwd T T' hle eT hact) x).imp fun _ hx' =>
    (congrArg (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) hx').trans
      (map_id_symm eT.symm (E.tie.jD T x))

set_option maxHeartbeats 800000 in
include hact in
theorem modules_eq (h0 : K0 K' = K0 K) (a1 : ∀ x, ∃ x', E'.tie.io x' = E.tie.io x)
    (a2 : ∀ x, ∃ x', E.tie.io x' = E'.tie.io x) (e1 : ∀ x, ∃ x', E'.tie.ioE x' = E.tie.ioE x)
    (e2 : ∀ x, ∃ x', E.tie.ioE x' = E'.tie.ioE x) (hQ : E'.tie.io W'.Q = E.tie.io W.Q)
    (hinj : Function.Injective E'.tie.ioE)
    (hb : IsCrys (P.PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (AA K LL) ↥(W.N T)))
    (h10 : IsCrys (P.PD K') T'.ρ → p10 W' T') :
    (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) '' Set.range (E'.tie.jD T') =
      Set.range (E.tie.jD T) ∧ (IsCrys (P.PD K) T.ρ → IsCrys (P.PD K') T'.ρ →
      (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) ''
        (E'.tie.jD T' '' (W'.N T' : Set (W'.DD T'))) = E.tie.jD T '' (W.N T : Set (W.DD T))) := by
  have d1 := jD_mem_sit E' E T' T h0 e2 eT.toLinearMap (act_fwd T T' hle eT hact)
  have d2 := jD_bwd E E' T T' hle eT hact h0.symm e1
  refine ⟨Set.Subset.antisymm ?_ ?_, fun hT hT' => ?_⟩
  · rintro _ ⟨_, ⟨x', rfl⟩, rfl⟩
    exact d1 x'
  · rintro _ ⟨x, rfl⟩
    obtain ⟨x', hx'⟩ := d2 x
    exact ⟨_, ⟨x', rfl⟩, hx'⟩
  · exact (hb hT).elim fun b => N_eq E.tie E'.tie T T' eT hT (h10 hT') b hinj a1 a2 e1 hQ d2 d1
      fun g' => ⟨⟨(g' : GQ l), GK_le hle g'.2⟩, rfl, hact g'⟩

end Two


set_option maxHeartbeats 800000 in
theorem base_indep : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → let W' := (HW l).W K' s LL h'; let E' := ((F l).E K' s LL h').tie; Set.range E.io = Set.range E'.io ∧ Set.range E.ioE = Set.range E'.ioE ∧ ∀ (T : Lt K LL) (T' : Lt K' LL) (eT : ↥T'.L.T ≃ₗ[↥(OL LL)] ↥T.L.T), (∀ (g : ↥(GK K')) (t : ↥T'.L.T), eT (T'.actT g t) = T.actT ⟨(g : GQ l), GK_le hle g.2⟩ (eT t)) → (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) '' Set.range (E'.jD T') = Set.range (E.jD T) ∧ (IsCrys ((D.loc l).PD K) T.ρ → IsCrys ((D.loc l).PD K') T'.ρ → (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) '' (E'.jD T' '' (W'.N T' : Set (W'.DD T'))) = E.jD T '' (W.N T : Set (W.DD T))) := by
  intro D HW F l _ K s LL h W E K' h' hle h0 W' E'
  have a1 := (rings_mem D HW F l K s LL h K' h' h0.symm).1
  have e1 := (rings_mem D HW F l K s LL h K' h' h0.symm).2
  have a2 := (rings_mem D HW F l K' s LL h' K h h0).1
  have e2 := (rings_mem D HW F l K' s LL h' K h h0).2
  have q := (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.1
  have q1 := (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').2.1
  have q2 := (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').2.2.2.1
  refine ⟨?_, ?_, fun T T' eT hact => ?_⟩
  · exact Set.Subset.antisymm (Set.range_subset_iff.2 a1) (Set.range_subset_iff.2 a2)
  · exact Set.Subset.antisymm (Set.range_subset_iff.2 e1) (Set.range_subset_iff.2 e2)
  have hb := N_basis D HW F l K s LL h T
  have h10 : IsCrys ((D.loc l).PD K') T'.ρ → p10 ((HW l).W K' s LL h') T' := GlobalTheory.NL.FrobeniusMatrixUniqueness.main D HW F l K' s LL h' T'
  exact modules_eq ((F l).E K s LL h) ((F l).E K' s LL h') T T' hle eT hact h0 a1 a2 e1 e2 (q1.trans q.symm)
    q2 hb h10

end GlobalTheory.NL.BaseField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesEqOfOpposite
section
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

noncomputable section

namespace GlobalTheory.SerSys.Opp

open GlobalTheory.GLq.Opp



variable {g : ℕ} [Fact g.Prime] {k l n : ℕ}

theorem blk_eq (x : Gn g k) (y : Gn g l) : blk k l (k + l) x y = par finSumFinEquiv x 0 y := by
  have h : (fun i j : Fin (k + l) => if (i : ℕ) < k ∧ (j : ℕ) < k then entN (x : Mt g k) i j
      else if k ≤ (i : ℕ) ∧ k ≤ (j : ℕ) then entN (y : Mt g l) (i - k) (j - k) else 0) =
      ((par finSumFinEquiv x 0 y : Gn g (k + l)) : Mt g (k + l)) := by
    funext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [par_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp [entN]
    · have := i.2
      simp [entN]
    · have := j.2
      simp [entN]
    · simp [entN]
  unfold blk
  rw [h, toG, dite_eq_left (Units.isUnit _), IsUnit.unit_of_val_units]

theorem eq_par (z : Gn g (k + l)) (h0 : InPar k (z : Mt g (k + l))) (h1 : tl k (z : Mt g (k + l)) = 1)
    (h2 : br k l (z : Mt g (k + l)) = 1) : ∃ B, z = par finSumFinEquiv 1 B 1 := by
  have e1 : ∀ (M : Mt g (k + l)) (i j : Fin k), tl k M i j = M (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j)) := by
    intro M i j
    have hi := i.2
    have hj := j.2
    rw [GlobalTheory.GLq.tl, entN, dite_eq_left ⟨by omega, by omega⟩]
    rfl
  have e2 : ∀ (M : Mt g (k + l)) (i j : Fin l), br k l M i j = M (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j)) := by
    intro M i j
    have hi := i.2
    have hj := j.2
    rw [br, entN, dite_eq_left ⟨by omega, by omega⟩]
    rfl
  refine ⟨Matrix.of fun i j => (z : Mt g (k + l)) (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j)), ?_⟩
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [par_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [← e1 (z : Mt g (k + l)) i j, h1]; simp
  · simp
  · rw [h0 _ _ (by simp) (by simp)]; simp
  · rw [← e2 (z : Mt g (k + l)) i j, h2]; simp

end GlobalTheory.SerSys.Opp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedHomComparisonCompatibleEnvelopeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratifiedHom_comparison_compatible_envelope : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S), bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) → (∀ g : ↥(GK K), S'.ε bk.ι ((ainfHom K g).comp bk.ι) * Y.map (BK.hf ((ainfHom K g).comp bk.ι)) = Y.map (BK.hf bk.ι) * S.ε bk.ι ((ainfHom K g).comp bk.ι)) → S'.ε En.inl En.inr * Y.map (BK.hf En.inr) = Y.map (BK.hf En.inl) * S.ε En.inl En.inr := by
  first | exact @GlobalTheory.BSP.strat_eps_compat_env | exact GlobalTheory.BSP.strat_eps_compat_env | (intros; apply GlobalTheory.BSP.strat_eps_compat_env <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystallineStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_fundamental_exact_sequence_crystalline : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V], (∀ (u : V ⊗[ℚ_[l]] P.R.B) (w : V ⊗[ℚ_[l]] P.R.BdR), ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := LL) (V := V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := V) x = u ∧ ιV (P.PD K) (LL := LL) (V := V) x - y = w) ∧ ∀ x : V ⊗[ℚ_[l]] P.R.B, φVB (P.PD K) (LL := LL) (V := V) x = x → ιV (P.PD K) (LL := LL) (V := V) x ∈ FilV (P.PD K) (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
  first | exact @GlobalTheory.FundSeq.tensor_fundamental_sequence | exact GlobalTheory.FundSeq.tensor_fundamental_sequence | (intros; apply GlobalTheory.FundSeq.tensor_fundamental_sequence <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedMatrixCongruenceLiftSequence
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.LimLink

theorem dvd_iff_map_eq {R : Type*} [CommRing R] {p q : Type*} (a : R) (A B : Matrix p q R) :
    (∀ i j, a ∣ (A - B) i j) ↔
      A.map (Ideal.Quotient.mk (Ideal.span {a})) = B.map (Ideal.Quotient.mk (Ideal.span {a})) := by
  first
  | exact @_root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq
  | exact _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq
  | (apply _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq ..)

theorem map_smul_ringHom {R S : Type*} [CommRing R] [CommRing S] {p q : Type*} (f : R →+* S) (r : R)
    (A : Matrix p q R) : (r • A).map f = f r • A.map f := by
  ext i j; simp

end GlobalTheory.BKLim.LimLink

open GlobalTheory.BKLim.LimLink in
theorem GlobalTheory.BKLim.limit_basis_link_mod : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (tw.d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v)) → ∀ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (T : Matrix (Fin d) (Fin d) (WCb l)), Y.map (inclW l) = inclW l τ ^ N • T → (∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∀ n, ∃ m, n ≤ m ∧ ∃ (Rn : Matrix (Fin d) (Fin (tw.d' m)) bk.S) (Q : Matrix (Fin (tw.d' m)) (Fin d) (Ainf l)), (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi m) * (F m).T - T * Rn.map bk.evW) i j) ∧ ∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (Rn.map bk.ev * Q).map (inclW l) - inclW l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j := by
  intro l _ K bk τ hτ d N ρ tw F T0 R H1 H2 H3 Y T hY H5 n
  obtain ⟨hu, -, -, -⟩ := _root_.GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have huN : IsUnit (inclW l τ ^ N) := hu.pow N
  obtain ⟨π, key, key'⟩ : ∃ π : WCb l →+* (WCb l ⧸ Ideal.span {(l : WCb l) ^ n}),
      (∀ {p q : ℕ} (A B : Matrix (Fin p) (Fin q) (WCb l)),
        (∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) → A.map π = B.map π) ∧
      (∀ {p q : ℕ} (A B : Matrix (Fin p) (Fin q) (WCb l)),
        A.map π = B.map π → ∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) :=
    ⟨_, fun A B => (dvd_iff_map_eq _ A B).1, fun A B => (dvd_iff_map_eq _ A B).2⟩
  obtain ⟨m, hnm, hm⟩ := H2 n
  have hcol : ∀ j : Fin (tw.d' m), ∃ (v : Fin d → WCb l) (c : Fin d → bk.S),
      (∀ i, (l : WCb l) ^ n ∣ v i - R m i j) ∧ T0 *ᵥ v = T *ᵥ fun a => bk.evW (c a) := by
    intro j
    obtain ⟨v, hv1, hv2⟩ := hm (Pi.single j 1)
    obtain ⟨hOE, y, hy⟩ := H3 v hv2
    obtain ⟨c, hc⟩ := H5 y ⟨v, hOE, hy⟩
    refine ⟨v, c, ?_, ?_⟩
    · intro i
      have hs : (fun a => bk.evW ((Pi.single j (1 : bk.S) : Fin (tw.d' m) → bk.S) a))
          = Pi.single j 1 := by
        funext a; by_cases h : a = j
        · subst h; simp
        · simp [Pi.single_apply, h]
      have := hv1 i
      rw [hs] at this
      simpa [Matrix.mulVec_single_one] using this
    · have h1 : (fun i => inclW l (y i)) = inclW l τ ^ N • (T *ᵥ fun a => bk.evW (c a)) := by
        rw [hc]; funext i
        rw [RingHom.map_mulVec, hY, Matrix.smul_mulVec]
        rfl
      rw [hy] at h1
      exact huN.smul_left_cancel.1 h1
  choose V C hV hVC using hcol
  let Rn : Matrix (Fin d) (Fin (tw.d' m)) bk.S := Matrix.of fun i j => C j i
  have hTR : T * Rn.map bk.evW = T0 * Matrix.of (fun i j => V j i) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hVC j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Rn]
    exact this.symm
  have hfirst : (zW (tw.Pi m) * (F m).T).map π = (T * Rn.map bk.evW).map π := by
    have e1 : (zW (tw.Pi m) * (F m).T).map π = (T0 * R m).map π :=
      key _ _ (fun i j => (pow_dvd_pow _ hnm).trans (H1 m i j))
    have e2 : (R m).map π = (Matrix.of fun i j => V j i).map π :=
      key _ _ (fun i j => by
        have := hV j i
        rw [← dvd_neg]; simpa [neg_sub] using this)
    rw [e1, hTR, Matrix.map_mul, Matrix.map_mul, e2]
  obtain ⟨Ym, Y'm, hYm, hYY⟩ :=
    _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N (tw.d' m) (fun g => (tw.ρ' m g).val) (F m)
  obtain ⟨Sm, hSm⟩ := (tw.onto m).surj
  refine ⟨m, hnm, Rn, Y'm * Sm.map (algebraMap ℤ_[l] (Ainf l)), key' _ _ hfirst, ?_⟩
  have hinc : ∀ x : ℤ_[l], inclW l (algebraMap ℤ_[l] (Ainf l) x) = algebraMap ℤ_[l] (WCb l) x :=
    fun x => (inclWA l).commutes x
  have hFY : (F m).T * Y'm.map (inclW l) = inclW l τ ^ N • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (WCb l)) := by
    apply huN.smul_left_cancel.1
    rw [← Matrix.smul_mul, ← hYm, ← Matrix.map_mul, hYY, map_smul_ringHom,
      Matrix.map_one _ (map_zero _) (map_one _), smul_smul, map_pow, ← pow_add, two_mul]
  have hQ : ((Rn.map bk.ev) * (Y'm * Sm.map (algebraMap ℤ_[l] (Ainf l)))).map (inclW l)
      = Rn.map bk.evW * (Y'm.map (inclW l) * zW Sm) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map]
    congr 2
    ext i j
    simp [hinc]
  have hS1 : (zW (tw.Pi m * Sm)).map π = (1 : Matrix (Fin d) (Fin d) (WCb l)).map π := by
    apply key
    intro i j
    have e : (zW (tw.Pi m * Sm) - 1) i j = algebraMap ℤ_[l] (WCb l) ((tw.Pi m * Sm - 1 : Matrix (Fin d) (Fin d) ℤ_[l]) i j) := by
      simp only [zW, Matrix.sub_apply, Matrix.map_apply, map_sub]
      congr 1
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [e]
    refine (pow_dvd_pow _ hnm).trans ?_
    have := map_dvd (algebraMap ℤ_[l] (WCb l)) (hSm i j)
    simpa using this
  have hE : inclW l τ ^ N • (zW (tw.Pi m) * (F m).T * (Y'm.map (inclW l) * zW Sm))
      = inclW l τ ^ (2 * N) • zW (tw.Pi m * Sm) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (F m).T, hFY, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul,
      ← pow_add, ← two_mul]
    simp only [zW, Matrix.map_mul]
  apply key'
  calc (Y.map (inclW l) * (Rn.map bk.ev * (Y'm * Sm.map (algebraMap ℤ_[l] (Ainf l)))).map (inclW l)).map π
      = (inclW l τ ^ N • ((T * Rn.map bk.evW) * (Y'm.map (inclW l) * zW Sm))).map π := by
        rw [hQ, hY, Matrix.smul_mul, ← Matrix.mul_assoc]
    _ = (inclW l τ ^ N • ((zW (tw.Pi m) * (F m).T) * (Y'm.map (inclW l) * zW Sm))).map π := by
        rw [map_smul_ringHom, map_smul_ringHom, Matrix.map_mul, Matrix.map_mul (L := zW (tw.Pi m) * (F m).T), hfirst]
    _ = (inclW l τ ^ (2 * N) • zW (tw.Pi m * Sm)).map π := by rw [hE]
    _ = (inclW l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))).map π := by
        rw [map_smul_ringHom, map_smul_ringHom, hS1]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeComparisonDcris
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.CmpCris

theorem wachLattice_comparison_dcris (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : P3 D HW F Cm := by
  intro l _ K s LL h T hT
  obtain ⟨h1, h2, -, h4⟩ := cmp_iso D HW F Cm l K s LL h T hT
  refine ⟨fun x hx => ?_, h2, fun x k hk => h4 x k hk⟩
  obtain ⟨y, rfl⟩ := (h1 x).1 hx
  exact ⟨y, y.2, rfl⟩

end GlobalTheory.NL.CmpCris
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionsStdBelowLevelStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLattice_expansions_std_below_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 → Std (Di (HW l) h T i) (Lat C h T i ζ) := by
  first | exact @GlobalTheory.NL.LatLow.lat_low | exact GlobalTheory.NL.LatLow.lat_low | (intros; apply GlobalTheory.NL.LatLow.lat_low <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelicStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ), (∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g) → ∀ u : GL (Fin a) (Ad E), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → ∀ g : GA E a, f (u * g) = ψ (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) * f g := by
  first | exact @GlobalTheory.CuspGeneric.tri_law | exact GlobalTheory.CuspGeneric.tri_law | (intros; apply GlobalTheory.CuspGeneric.tri_law <;> assumption)
end

