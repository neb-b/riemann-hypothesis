module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0032
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.FiniteHeis

variable {D : D7}

noncomputable def heisLin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : Module.End ℂ (WO S T → ℂ) where
  toFun := heisO ψ S T u
  map_add' f g := by
    funext w
    simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by
    funext w
    simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem lineAt_fin {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    (show WO S T from lineAt θ τ z t).map (finPart D) = 0 :=
  (Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ T.rank S.rank τ z)).2.1 t

theorem heisO_comm_real (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {u x : WO S T} (hu : u.map (infPart D) = 0)
    (hx : x.map (finPart D) = 0) (g : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T x g) = heisO ψ S T x (heisO ψ S T u g) := by
  rw [GlobalTheory.OrientedHeis.heisO_heisO, GlobalTheory.OrientedHeis.heisO_heisO, (GlobalTheory.OrientedHeis.symplOH_fin_real hu hx).1,
    (GlobalTheory.OrientedHeis.symplOH_fin_real hu hx).2, add_comm]

theorem heisO_dRho (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {u : WO S T}
    (hu : u.map (infPart D) = 0) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    heisO ψ S T u (dRho (heisO ψ S T) θ τ z g) = dRho (heisO ψ S T) θ τ z (heisO ψ S T u g) := by
  funext x
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (heisO ψ S T u g) x) =
      fun t : ℝ => ψ (symplOH S T x u) * heisO ψ S T (lineAt θ τ z t) g (x + u) := by
    funext t
    rw [← heisO_comm_real ψ hu (lineAt_fin hθ τ z t) g]
    rfl
  show ψ (symplOH S T x u) * deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) g (x + u)) 0 =
    deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (heisO ψ S T u g) x) 0
  rw [e, deriv_const_mul_field]

theorem heisO_pureTensorO_of_finite : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsInfFam θ → ∀ sS sT BS BT f, (∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f φ)) → ∀ u : WO S T, u.map (infPart D) = 0 → heisO ψ S T u f = f → ∀ φ, heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT f φ := by
  intro D ψ θ S T hθ sS sT BS BT f _ u hu hf φ
  have h := (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) (heisLin ψ S T u)
    (fun k g _ => ⟨trivial, ?_⟩) f trivial φ).2
  · have hf' : heisLin ψ S T u f = f := hf
    rw [hf'] at h
    exact h
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll, aPlus, crea]
    rw [map_smul, map_sub, map_smul]
    show _ • (heisO ψ S T u (Datum.dRho _ _ _ _ _) - _ • heisO ψ S T u (Datum.dRho _ _ _ _ _)) = _
    rw [heisO_dRho ψ hθ hu, heisO_dRho ψ hθ hu]
    rfl

end GlobalTheory.Hk3.FiniteHeis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHomogeneousOfMemWeyl
section
noncomputable section

namespace GlobalTheory.LiftTypePrime

open NumberField MvPolynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

section Generic

open Formalism.GradedWeylDivisibility

variable {a b : ℕ} (hab : a ≤ b)

def subGen : MvPolynomial (Fin a × Fin a) ℤ →ₐ[ℤ] MvPolynomial (Fin b × Fin a) (MvPolynomial (Fin b × Fin b) ℤ) :=
  aeval fun v => ∑ β : Fin b, C (X (β, Fin.castLE hab v.2)) * X (β, v.1)

theorem aeval_subGen {A : Type} [CommRing A] (d : Fin b × Fin a → A) (y : Fin b × Fin b → A)
    (f : MvPolynomial (Fin a × Fin a) ℤ) :
    aeval (fun v : Fin a × Fin a => ∑ β : Fin b, y (β, Fin.castLE hab v.2) * d (β, v.1)) f =
      ∑ α ∈ (subGen hab f).support, aeval y ((subGen hab f).coeff α) * ∏ v ∈ α.support, d v ^ α v := by
  have h := eval₂_eq (aeval (R := ℤ) y).toRingHom d (subGen hab f)
  refine Eq.trans ?_ h
  have : (aeval (R := ℤ) (fun v : Fin a × Fin a => ∑ β : Fin b, y (β, Fin.castLE hab v.2) * d (β, v.1))).toRingHom =
      (eval₂Hom (aeval (R := ℤ) y).toRingHom d).comp (subGen hab).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => ?_
    simp [subGen]
  exact RingHom.congr_fun this f

theorem isHomogeneous_of_mem_weyl {ν : Fin a → ℕ} (hν : Antitone ν) {f : MvPolynomial (Fin a × Fin a) ℤ}
    (hf : f ∈ weyl ℤ a a le_rfl ν) : f.IsHomogeneous (∑ r, ν r) := by
  have h : IsWeightedHomogeneous (colW a a) f ν := (weylLeDual ℤ a a le_rfl ν hν hf).1
  intro m hm
  rw [← h hm]
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, colW]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Pi.single_apply]

theorem subGen_isHomogeneous {n : ℕ} {f : MvPolynomial (Fin a × Fin a) ℤ} (hf : f.IsHomogeneous n) :
    (subGen hab f).IsHomogeneous n := by
  have := hf.aeval (fun v : Fin a × Fin a => ∑ β : Fin b,
    (C (X (β, Fin.castLE hab v.2)) * X (β, v.1) : MvPolynomial (Fin b × Fin a) (MvPolynomial (Fin b × Fin b) ℤ)))
    (n := 1) (fun v => IsHomogeneous.sum _ _ _ fun β _ => isHomogeneous_C_mul_X _ _)
  rw [one_mul] at this
  exact this

theorem coeff_subGen_mem {ν : Fin a → ℕ} {ν' : Fin b → ℕ} (hν : Antitone ν')
    (h : ∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) {f : MvPolynomial (Fin a × Fin a) ℤ}
    (hf : f ∈ weyl ℤ a a le_rfl ν) (α : Fin b × Fin a →₀ ℕ) : (subGen hab f).coeff α ∈ weyl ℤ b b le_rfl ν' := by
  let S := MvPolynomial (Fin b × Fin a) ℤ
  let M : Matrix (Fin b) (Fin b) S := fun i β => if h : (i : ℕ) < a then X (β, ⟨i, h⟩) else 0
  have h1 := _root_.GlobalTheory.weyl_rename_castLE_mem ℤ a b hab ν ν' h f hf
  have hmap : ∀ g ∈ weyl ℤ b b le_rfl ν', map (algebraMap ℤ S) g ∈ weyl S b b le_rfl ν' := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact Submodule.subset_span ⟨w, by
        beta_reduce
        rw [← lclosedeq_hw_map (algebraMap ℤ S), lclosedeq_applyWord_map]⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := map (algebraMap ℤ S))]; exact add_mem hx hy
    | smul c x _ hx => rw [map_zsmul]; exact zsmul_mem hx c
  have h2 := _root_.GlobalTheory.WeylRowAll.rowAct_mem_weyl_square S b ν' hν M _ (hmap _ h1)
  let ψ : MvPolynomial (Fin b × Fin b) S →+* MvPolynomial (Fin b × Fin a) (MvPolynomial (Fin b × Fin b) ℤ) :=
    eval₂Hom (map (algebraMap ℤ _)) fun v => C (X v)
  have hψ : ∀ g : MvPolynomial (Fin b × Fin b) ℤ, ψ (map (algebraMap ℤ S) g) = C g := fun g => by
    have : ψ.comp (map (algebraMap ℤ S)) = C :=
      MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => by simp [ψ]
    exact RingHom.congr_fun this g
  have e : subGen hab f = ψ (rowAct S M (map (algebraMap ℤ S) (rename (fun v : Fin a × Fin a =>
      ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b)) f))) := by
    have : (subGen hab).toRingHom = ψ.comp ((rowAct S M).toRingHom.comp ((map (algebraMap ℤ S)).comp
        (rename (fun v : Fin a × Fin a => ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b))).toRingHom)) := by
      refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => ?_
      simp [subGen, rowAct, ψ, M, mul_comm]
      exact Finset.sum_congr rfl fun x _ => congrArg (· * _) (map_X _ _).symm
    exact RingHom.congr_fun this f
  rw [e]
  generalize rowAct S M _ = F at h2
  induction h2 using Submodule.span_induction generalizing α with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    have : applyWord S w (hw S le_rfl ν') = map (algebraMap ℤ S) (applyWord ℤ w (hw ℤ le_rfl ν')) := by
      rw [← lclosedeq_hw_map (algebraMap ℤ S), lclosedeq_applyWord_map]
    simp only [this, hψ, coeff_C]
    split_ifs
    · exact Submodule.subset_span ⟨w, rfl⟩
    · exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), AddMonoidAlgebra.coeff_add]; exact add_mem (hx α) (hy α)
  | smul c x _ hx =>
    classical
    rw [smul_eq_C_mul, map_mul, coeff_mul]
    refine Submodule.sum_mem _ fun p _ => ?_
    have : ψ (C c) = map (algebraMap ℤ _) c := by simp [ψ]
    rw [this, coeff_map, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hx _)

end Generic

section Integral

variable {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]}

variable {D : D7} {N : ℕ} {wt : D.what₂.Tau → DomWeight N}

variable {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {O : LiftObj D (D.chTw u μ)} {i : ℕ}

end Integral

section Subst

variable {D : D7} {N N' : ℕ}

end Subst

section Lift

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup}

theorem natW_anti {n : ℕ} (l : DomWeight n) : Antitone l.natW := fun _ _ h =>
  Int.toNat_le_toNat (sub_le_sub_right (l.anti h) _)

end Lift

end GlobalTheory.LiftTypePrime

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointEigenvectorsEqZeroOfSumEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem joint_eigenvectors_eq_zero_of_sum_eq_zero (ι κ M : Type) [AddCommGroup M] [Module ℂ M]
    (A : ι → Module.End ℂ M) (χ : κ → ι → ℂ) (v : κ → M) (s : Finset κ)
    (heig : ∀ k ∈ s, ∀ i, A i (v k) = χ k i • v k) (hinj : Set.InjOn χ s)
    (hsum : ∑ k ∈ s, v k = 0) : ∀ k ∈ s, v k = 0 := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty => simp
  | insert a s ha ih =>
    have hsum' : v a + ∑ k ∈ s, v k = 0 := by rwa [Finset.sum_insert ha] at hsum
    have hs : ∀ k ∈ s, v k = 0 := by
      intro k hk
      have hne : χ k ≠ χ a := by
        intro h
        have hka : k = a := hinj (by simp [hk]) (by simp) h
        exact ha (hka ▸ hk)
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have hw : (χ k i - χ a i) • v k = 0 := by
        refine ih (fun j => (χ j i - χ a i) • v j) ?_ ?_ ?_ k hk
        · intro j hj i'
          have h1 := heig j (Finset.mem_insert_of_mem hj) i'
          simp only [map_smul, h1]
          rw [smul_comm]
        · exact hinj.mono (by simp)
        · have h2 : A i (v a + ∑ k ∈ s, v k) - χ a i • (v a + ∑ k ∈ s, v k) = 0 := by
            rw [hsum']; simp
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_add (f := _), map_sum, heig a (Finset.mem_insert_self a s) i, smul_add, Finset.smul_sum,
            add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib] at h2
          rw [← h2]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [heig j (Finset.mem_insert_of_mem hj) i, sub_smul]
      exact (smul_eq_zero.mp hw).resolve_left (sub_ne_zero.mpr hi)
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simpa [Finset.sum_eq_zero hs] using hsum'
    · exact hs k hk

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationEqOfHeckeAgreementTwistLaws
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.LocSepTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem lpChar_zero_unr (w : PlE H) (χ : A.LP w) (hd : A.lpDim χ = 1) (hu : A.unr χ) :
    A.lpChar (A.lpZero w) χ = A.lpZero w := by
  have hu0 := A.lpZero_unr w
  have hc := A.unr_char _ _ hd hu0 hu
  have hcard := A.frobEig_card _ hc
  rw [A.lpDim_char _ _ hd, A.lpDim_zero] at hcard
  calc A.lpChar (A.lpZero w) χ = A.lpUnr w (A.frobEig (A.lpChar (A.lpZero w) χ)) := A.unr_eq_lpUnr _ hc
    _ = A.lpUnr w (A.frobEig (A.lpZero w)) := by rw [Multiset.card_eq_zero.mp hcard, A.frobEig_zero]
    _ = A.lpZero w := (A.unr_eq_lpUnr _ hu0).symm

theorem spehLoc_twist_of_laws (hC : GlobalTheory.RowTie.CharLaws N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H)
    (hz : A.lpChar (A.lpZero w) (A.locG χ w) = A.lpZero w) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  have hsum : ∀ a b : A.LP w, A.lpChar (A.lpSum a b) (A.locG χ w) =
      A.lpSum (A.lpChar a (A.locG χ w)) (A.lpChar b (A.locG χ w)) := fun a b => (hC w a b _ _ 0 hχ hχ).1
  have htw : ∀ (a : A.LP w) (s : ℝ), A.lpChar (A.lpTw a s) (A.locG χ w) = A.lpTw (A.lpChar a (A.locG χ w)) s :=
    fun a s => (hC w a a _ _ s hχ hχ).2.1
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact hz.symm
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, hsum, htw, A.locG_tw]

theorem isoLoc_twist_of_laws (hC : GlobalTheory.RowTie.CharLaws N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H)
    (hz : A.lpChar (A.lpZero w) (A.locG χ w) = A.lpZero w) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  induction S with
  | nil => exact hz.symm
  | cons p S ih =>
    change A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [ih, spehLoc_twist_of_laws N A hC p χ w hz, (hC w _ _ _ _ 0 hχ hχ).1]

theorem isoLoc_append_one (S : List (Part A.CG)) (q : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [q]) w = A.lpSum (isoLoc N A S w) (spehLoc N A q w) := by
  induction S with
  | nil =>
    change A.lpSum (spehLoc N A q w) (A.lpZero w) = A.lpSum (A.lpZero w) (spehLoc N A q w)
    exact A.lpSum_comm _ _
  | cons p S ih =>
    change A.lpSum (spehLoc N A p w) (isoLoc N A (S ++ [q]) w) =
      A.lpSum (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (spehLoc N A q w)
    rw [ih, A.lpSum_assoc]

theorem heckePol_coeff (i : N.Loc) (x : N.X i) (w : PlE H) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ R.nV) :
    (heckePol N i x w).coeff (R.nV - k) =
      (-1 : N.O i) ^ k * ((normV w : ℕ) : N.O i) ^ (k * (k - 1) / 2) * ((N.hT i w k : N.X i → N.O i) x) := by
  unfold heckePol
  exact GlobalTheory.PtLocalEig.coeff_monic_poly_sum R.nV k hk1 hk2
    (fun k' => (-1 : N.O i) ^ k' * ((normV w : ℕ) : N.O i) ^ (k' * (k' - 1) / 2) * ((N.hT i w k' : N.X i → N.O i) x))

theorem main : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → GlobalTheory.RowTie.CharLaws D.nd D.naut →
    (∀ (i i' : D.nd.Loc) (σ : D.what₂.FT) (v : PlE D.host), IsSplitPl D.host v →
      D.naut.locW i σ v = D.naut.locW i' σ v) →
    (∀ i i' : D.nd.Loc, D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' → D.naut.muC i = D.naut.muC i') →
    KillingConditions.LocalisationUniqueness D := by
  intro D M HT hC hW hmu
  unfold KillingConditions.LocalisationUniqueness
  intro i i' _ hj hw σ _ hA hA'
  by_contra hne
  obtain ⟨φ, hφ⟩ := HT.sameO i i' hj hw
  obtain ⟨Sig, hSig, x, hx⟩ := hA
  obtain ⟨Sig', hSig', x', hx'⟩ := hA'
  obtain ⟨v, k, hv, hv', hk1, hk2, hunit⟩ := HT.sep i i' φ hφ hj hw hne x x'
  obtain ⟨p, hp1, hp2⟩ := hx v hv
  obtain ⟨p', hp1', hp2'⟩ := hx' v hv'
  have hinj' : Function.Injective (iotaO D.nd D.naut i') := by
    unfold iotaO
    simp only [RingHom.coe_comp]
    exact (D.naut.iotaQC i').injective.comp ((D.naut.iotaQ i').injective.comp
      (IsFractionRing.injective (D.nd.O i') (FractionRing (D.nd.O i'))))
  have hmuP : muPart D.nd D.naut i = muPart D.nd D.naut i' := by
    unfold muPart; rw [hmu i i' hj hw]
  have hz := lpChar_zero_unr D.nd D.naut v (D.naut.locG D.naut.etaTinv v) (D.naut.locG_dim _ v)
    (D.naut.etaTinv_def v).1
  have hpar : isoLoc D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) v =
      isoLoc D.nd D.naut (twistIso D.nd D.naut (Sig' ++ [muPart D.nd D.naut i']) D.naut.etaTinv) v := by
    rw [isoLoc_twist_of_laws D.nd D.naut hC _ _ v hz, isoLoc_twist_of_laws D.nd D.naut hC _ _ v hz,
      isoLoc_append_one, isoLoc_append_one, hSig.2.2 v hv.1, hSig'.2.2 v hv'.1, hW i i' σ v hv.1, hmuP]
  have hpp : p.map (φ : D.nd.O i →+* D.nd.O i') = p' := by
    apply Polynomial.map_injective (iotaO D.nd D.naut i') hinj'
    rw [Polynomial.map_map, hp1', ← hpar, ← hp1]
    congr 1
    exact RingHom.ext fun z => (hφ z).symm
  set n := D.R.nV - k
  have e1 : IsLocalRing.residue (D.nd.O i) (p.coeff n) =
      IsLocalRing.residue (D.nd.O i) ((heckePol D.nd i x v).coeff n) := by
    have := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P n) hp2
    simpa only [Polynomial.coeff_map] using this
  have e2 : IsLocalRing.residue (D.nd.O i') (p'.coeff n) =
      IsLocalRing.residue (D.nd.O i') ((heckePol D.nd i' x' v).coeff n) := by
    have := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P n) hp2'
    simpa only [Polynomial.coeff_map] using this
  have e3 := GlobalTheory.PtLocalEig.residue_map_equiv φ e1
  have hcp : φ (p.coeff n) = p'.coeff n := by
    rw [← hpp, Polynomial.coeff_map]; rfl
  have hφc : φ ((-1 : D.nd.O i) ^ k * ((normV v : ℕ) : D.nd.O i) ^ (k * (k - 1) / 2) *
      ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x)) = (-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2) *
      φ ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [hcp, e2, heckePol_coeff D.nd i x v k hk1 hk2, heckePol_coeff D.nd i' x' v k hk1 hk2, hφc] at e3
  have hq := GlobalTheory.PtLocalEig.normV_unit D i' v hv'.2.1
  have hc : IsUnit ((-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2)) :=
    ((isUnit_one.neg).pow k).mul (hq.pow _)
  have hdiff : IsLocalRing.residue (D.nd.O i')
      ((-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2) *
        (φ ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) - (D.nd.hT i' v k : D.nd.X i' → D.nd.O i') x')) = 0 := by
    rw [mul_sub, map_sub, e3, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hdiff
  exact hdiff (hc.mul hunit)

end GlobalTheory.LocSepTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexIntegralTranslationInvariance
section
noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mulVec_mem_intVec_of_int {a b : ℕ} {M : Matrix (Fin a) (Fin b) L}
    (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) {v : Fin b → L} (hv : v ∈ intVec L b) :
    M.mulVec v ∈ intVec L a := by
  rw [mem_intVec] at hv ⊢
  intro i
  change (∑ j, M i j * v j) ∈ Formalism.UG.intL L
  exact sum_mem fun j _ => mul_mem (hM i j) (hv j)

theorem entry_mem_of_mem_GLint {n : ℕ} {g : GL (Fin n) L} (hg : g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L))
    (i j : Fin n) : (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  obtain ⟨g0, rfl⟩ := hg
  exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2

theorem latIdx_add_int {a b : ℕ} (x u : Matrix (Fin a) (Fin b) L) (hu : u ∈ intMat L a b) :
    latIdx (x + u) = latIdx x := by
  have hf : (fun v : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec (x + u) (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a)) =
      fun v : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a) := by
    funext v
    rw [Matrix.add_mulVec, QuotientAddGroup.mk_add,
      (QuotientAddGroup.eq_zero_iff _).2 (mulVec_mem_intVec_of_int ((mem_intMat u).1 hu) v.2), add_zero]
  unfold latIdx
  rw [hf]

def quotMul {a : ℕ} (M : Matrix (Fin a) (Fin a) L) (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) :
    (Fin a → L) ⧸ intVec L a →+ (Fin a → L) ⧸ intVec L a :=
  QuotientAddGroup.map (intVec L a) (intVec L a) (Matrix.mulVecLin M).toAddMonoidHom
    fun _ hv => mulVec_mem_intVec_of_int hM hv

theorem quotMul_mk {a : ℕ} (M : Matrix (Fin a) (Fin a) L) (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) (v : Fin a → L) :
    quotMul M hM (QuotientAddGroup.mk v) = QuotientAddGroup.mk (M.mulVec v) := rfl

theorem latIdx_GLint_mul {a b : ℕ} (x : Matrix (Fin a) (Fin b) L) (h : GL (Fin a) L)
    (hh : h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L)) :
    latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = latIdx x := by
  have h1 := entry_mem_of_mem_GLint hh
  have h2 := entry_mem_of_mem_GLint (inv_mem hh)
  have hinj : Function.Injective (quotMul (h : Matrix (Fin a) (Fin a) L) h1) := by
    have hl : Function.LeftInverse (quotMul ((h⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) h2)
        (quotMul (h : Matrix (Fin a) (Fin a) L) h1) := by
      intro q
      induction q using QuotientAddGroup.induction_on with
      | H v =>
        rw [quotMul_mk, quotMul_mk, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
    exact hl.injective
  have hr : (Set.range fun v : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec ((h : Matrix (Fin a) (Fin a) L) * x) (v : Fin b → L)) :
        (Fin a → L) ⧸ intVec L a)) =
      quotMul (h : Matrix (Fin a) (Fin a) L) h1 '' Set.range fun v : intVec L b =>
        (QuotientAddGroup.mk (Matrix.mulVec x (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a) := by
    rw [← Set.range_comp]
    congr 1
    funext v
    exact congrArg QuotientAddGroup.mk (Matrix.mulVec_mulVec _ _ _).symm
  unfold latIdx
  rw [hr, Nat.card_image_of_injective hinj]

theorem latIdx_invariance : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) (x : Matrix (Fin a) (Fin b) L),
    (∀ u ∈ GlobalTheory.Hk3.HoweDuality.intMat L a b, GlobalTheory.Hk3.HoweDuality.latIdx (x + u) = GlobalTheory.Hk3.HoweDuality.latIdx x) ∧
    ∀ h : GL (Fin a) L, h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      GlobalTheory.Hk3.HoweDuality.latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = GlobalTheory.Hk3.HoweDuality.latIdx x :=
  fun _ _ _ _ _ x => ⟨fun u hu => latIdx_add_int x u hu, fun h hh => latIdx_GLint_mul x h hh⟩

end GlobalTheory.Hk3.HoweDuality

end
end

