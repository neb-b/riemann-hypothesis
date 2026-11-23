module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.FrameTangent
open MvPolynomial (X C)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Jets

variable {S : Type} [CommRing S]

abbrev z {κ : Type} (m : ℕ) (j : κ) : Jet S κ m := Ideal.Quotient.mk _ (X j)

theorem jext {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra S A] {ψ₁ ψ₂ : Jet S κ m →ₐ[S] A}
    (h : ∀ j, ψ₁ (z m j) = ψ₂ (z m j)) : ψ₁ = ψ₂ :=
  Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext h)

theorem jetMap_z {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (h) (s : κ) :
    (jetMap φ h : Jet S κ m →ₐ[S] Jet S κ' m) (z m s) = Ideal.Quotient.mk _ (φ s) := by
  show Ideal.Quotient.mkₐ S _ (MvPolynomial.aeval φ (MvPolynomial.X s)) = _
  rw [MvPolynomial.aeval_X]; rfl

theorem jetAug_z {κ : Type} (m : ℕ) (s : κ) : (jetAug : Jet S κ m →ₐ[S] S) (z m s) = 0 :=
  MvPolynomial.aeval_X (fun _ => (0 : S)) s


variable (S) in
abbrev jIn (d m : ℕ) : Jet S (Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m := jetIn (0 : Fin 1)


variable (S) in
def jOut (d m : ℕ) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin d) m := jetMap (fun p => X p.2) fun _ => X_mem_orig _

variable {d : ℕ}

theorem jet_inclusion_z (m : ℕ) (j : Fin d) : jIn S d m (z m j) = z m (0, j) := jetMap_z m _ _ j

theorem jOut_jIn (m : ℕ) : (jOut S d m).comp (jIn S d m) = AlgHom.id S _ :=
  jext fun j => by rw [AlgHom.comp_apply, jet_inclusion_z]; exact jetMap_z m _ _ _

theorem jIn_jOut (m : ℕ) : (jIn S d m).comp (jOut S d m) = AlgHom.id S _ :=
  jext fun p => by
    obtain ⟨i, j⟩ := p
    obtain rfl := Subsingleton.elim i 0
    rw [AlgHom.comp_apply, jOut, jetMap_z]
    exact jet_inclusion_z m j

theorem aug_jIn (m : ℕ) : (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S).comp (jIn S d m) = jetAug :=
  jext fun j => by rw [AlgHom.comp_apply, jet_inclusion_z, jetAug_z, jetAug_z]

theorem trunc_jIn (m : ℕ) : (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _).comp (jIn S d (m + 1)) =
    (jIn S d m).comp jetTrunc :=
  jext fun j => by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, jet_inclusion_z]
    exact (jet_inclusion_z m j).symm

theorem tan_jIn (j : Fin d) :
    (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S).comp (jIn S d 1) =
      jetVec (Pi.single j 1) :=
  jext fun i => by
    rw [AlgHom.comp_apply, jetVec_X]
    refine (congrArg _ (jet_inclusion_z 1 i)).trans ?_
    show MvPolynomial.aeval (fun i => if i = ((0 : Fin 1), j) then (DualNumber.eps : DualNumber S) else 0)
      (MvPolynomial.X ((0 : Fin 1), i)) = _
    rw [MvPolynomial.aeval_X]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (fun h => hij (Prod.ext_iff.1 h).2), Pi.single_eq_of_ne hij, zero_smul]

theorem jetVec_z_one {σ : Type} (c : σ → S) (i : σ) : jetVec c (z 1 i) = TrivSqZeroExt.inr (c i) := by
  rw [jetVec_X]
  ext <;> simp

end Jets

section Fam

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem algMap_eq {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (f : A →ₐ[S] B) :
    algMap x0 f = homAt x0 f := rfl

theorem hcomp {A B D : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] [CommRing D] [Algebra S D]
    (f : A →ₐ[S] B) (g : B →ₐ[S] D) {G : Over X0} (y : overAt x0 A ⟶ G) :
    homAt x0 g ≫ homAt x0 f ≫ y = homAt x0 (g.comp f) ≫ y := by
  rw [← Category.assoc, homAt_comp]

def famEquiv (G : Over X0) (d : ℕ) : JetPts G x0 d ≃ ∀ m, jOG x0 d m 1 ⟶ G where
  toFun j m := homAt x0 (jIn S d m) ≫ j m
  invFun x m := homAt x0 (jOut S d m) ≫ x m
  left_inv j := funext fun m => by
    change homAt x0 _ ≫ homAt x0 _ ≫ j m = j m
    rw [hcomp, jOut_jIn, homAt_id, Category.id_comp]
  right_inv x := funext fun m => by
    change homAt x0 _ ≫ homAt x0 _ ≫ x m = x m
    rw [hcomp, jIn_jOut, homAt_id, Category.id_comp]

theorem famEquiv_apply {G : Over X0} {d : ℕ} (j : JetPts G x0 d) (m : ℕ) :
    famEquiv x0 G d j m = homAt x0 (jIn S d m) ≫ j m := rfl

theorem jIn_cancel {G : Over X0} {d m : ℕ} {y y' : overAt x0 (Jet S (Fin d) m) ⟶ G}
    (h : homAt x0 (jIn S d m) ≫ y = homAt x0 (jIn S d m) ≫ y') : y = y' := by
  have := congrArg (homAt x0 (jOut S d m) ≫ ·) h
  simpa only [hcomp, jOut_jIn, homAt_id, Category.id_comp] using this

variable {G : Over X0} [GrpObj G]

theorem split_axes (W : overAt x0 (TrivSqZeroExt S (S × S)) ⟶ G)
    (h0 : homAt x0 (TrivSqZeroExt.fstHom S S (S × S)) ≫ W = 1) :
    W = (homAt x0 (tm (LinearMap.inl S S S)) ≫ homAt x0 (tm (LinearMap.fst S S S)) ≫ W) *
      (homAt x0 (tm (LinearMap.inr S S S)) ≫ homAt x0 (tm (LinearMap.snd S S S)) ≫ W) := by
  have hz : homAt x0 (tm (0 : S × S →ₗ[S] S)) ≫ W = 1 := by
    have e : tm (0 : S × S →ₗ[S] S) = (Algebra.ofId S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S (S × S)) := by
      apply AlgHom.ext
      intro r
      ext <;> simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl]
    rw [e, ← hcomp, h0, MonObj.comp_one]
  apply Over.OverMorphism.ext
  apply spec_ext_two (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S)
    (tm (LinearMap.snd S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S)
  · intro y
    refine ⟨tm (LinearMap.inl S S S) y, ?_⟩
    ext <;> simp
  · intro x hx
    have h1 : x.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hx
    ext <;> simp [h1]
  · intro x hx hx'
    have h1 : x.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hx
    have h2 : x.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd hx
    have h3 : x.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd hx'
    ext <;> simp [h1, h2, h3]
  · have h : homAt x0 (tm (LinearMap.fst S S S)) ≫ W = homAt x0 (tm (LinearMap.fst S S S)) ≫
        ((homAt x0 (tm (LinearMap.inl S S S)) ≫ homAt x0 (tm (LinearMap.fst S S S)) ≫ W) *
          (homAt x0 (tm (LinearMap.inr S S S)) ≫ homAt x0 (tm (LinearMap.snd S S S)) ≫ W)) := by
      rw [MonObj.comp_mul]
      simp only [hcomp, ← TrivSqZeroExt.map_comp_map, ← LinearMap.comp_assoc, LinearMap.fst_comp_inl,
        LinearMap.fst_comp_inr, LinearMap.id_comp, LinearMap.zero_comp]
      rw [hz, _root_.mul_one]
    exact congrArg (fun φ => φ.left) h
  · have h : homAt x0 (tm (LinearMap.snd S S S)) ≫ W = homAt x0 (tm (LinearMap.snd S S S)) ≫
        ((homAt x0 (tm (LinearMap.inl S S S)) ≫ homAt x0 (tm (LinearMap.fst S S S)) ≫ W) *
          (homAt x0 (tm (LinearMap.inr S S S)) ≫ homAt x0 (tm (LinearMap.snd S S S)) ≫ W)) := by
      rw [MonObj.comp_mul]
      simp only [hcomp, ← TrivSqZeroExt.map_comp_map, ← LinearMap.comp_assoc, LinearMap.snd_comp_inl,
        LinearMap.snd_comp_inr, LinearMap.id_comp, LinearMap.zero_comp]
      rw [hz, _root_.one_mul]
    exact congrArg (fun φ => φ.left) h

variable {σ : Type} (y : overAt x0 (Jet S σ 1) ⟶ G) (h0 : homAt x0 (jetAug : Jet S σ 1 →ₐ[S] S) ≫ y = 1)

theorem smT_vec (a : S) (c : σ → S) :
    smT x0 a (homAt x0 (jetVec c) ≫ y) = homAt x0 (jetVec (a • c)) ≫ y := by
  rw [smT, hcomp]
  congr 2
  refine jext fun i => ?_
  rw [AlgHom.comp_apply, jetVec_z_one, jetVec_z_one]
  ext <;> simp [mul_comm]

include h0

theorem vec_zero : homAt x0 (jetVec (0 : σ → S)) ≫ y = 1 := by
  have e : jetVec (0 : σ → S) = (Algebra.ofId S (DualNumber S)).comp jetAug :=
    jext fun i => by rw [jetVec_z_one, AlgHom.comp_apply, jetAug_z, map_zero]; simp
  rw [e, ← hcomp, h0, MonObj.comp_one]

theorem vec_add (c c' : σ → S) :
    homAt x0 (jetVec (c + c')) ≫ y = (homAt x0 (jetVec c) ≫ y) * (homAt x0 (jetVec c') ≫ y) := by
  let Φ : Jet S σ 1 →ₐ[S] TrivSqZeroExt S (S × S) :=
    Chart.jetLift S _ Chart.delta_sq (fun i => TrivSqZeroExt.inr (c i, c' i)) (fun i => (RingHom.mem_ker).mpr rfl)
  have hΦ : ∀ i, Φ (z 1 i) = TrivSqZeroExt.inr (c i, c' i) := fun i => Chart.jetLift_zR _ _ _ _ i
  have e : ∀ (l : S × S →ₗ[S] S) (b : σ → S), (∀ i, l (c i, c' i) = b i) → (tm l).comp Φ = jetVec b :=
    fun l b h => jext fun i => by rw [AlgHom.comp_apply, hΦ, jetVec_z_one, TrivSqZeroExt.map_inr, h]
  have key := split_axes x0 (homAt x0 Φ ≫ y) (by
    have : (TrivSqZeroExt.fstHom S S (S × S)).comp Φ = jetAug :=
      jext fun i => by rw [AlgHom.comp_apply, hΦ, jetAug_z]; rfl
    rw [hcomp, this, h0])
  rw [hcomp x0 Φ (tm (LinearMap.fst S S S)), hcomp x0 Φ (tm (LinearMap.snd S S S)), e _ c fun _ => rfl,
    e _ c' fun _ => rfl] at key
  have h := congrArg (homAt x0 (tm (LinearMap.coprod (LinearMap.id : S →ₗ[S] S) LinearMap.id)) ≫ ·) key
  beta_reduce at h
  rw [MonObj.comp_mul, hcomp, e _ (c + c') (fun _ => rfl), hcomp x0 (tm (LinearMap.inl S S S)),
    hcomp x0 (tm (LinearMap.inr S S S)), ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
    LinearMap.coprod_inl, LinearMap.coprod_inr, TrivSqZeroExt.map_id, homAt_id, Category.id_comp,
    Category.id_comp] at h
  exact h

variable [IsCommMonObj G]

def dif : (σ → S) →ₗ[S] TanM x0 G where
  toFun c := mkT (homAt x0 (jetVec c) ≫ y) (by rw [smT_vec, zero_smul, vec_zero x0 y h0])
  map_add' c c' := tv_injective (vec_add x0 y h0 c c')
  map_smul' a c := tv_injective (smT_vec x0 y a c).symm

theorem tv_dif (c : σ → S) : tv (dif x0 y h0 c) = homAt x0 (jetVec c) ≫ y := rfl

end Fam

section Param

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {G : Over X0} [GrpObj G] [IsCommMonObj G] {d : ℕ}
  {j : JetPts G x0 d}


set_option maxHeartbeats 800000 in
theorem param_of_dif_bijective (hG : Smooth G.hom)
    (ht : ∀ m, homAt x0 (jetTrunc : Jet S (Fin d) (m + 1) →ₐ[S] Jet S (Fin d) m) ≫ j (m + 1) = j m)
    (h0 : ∀ m, homAt x0 (jetAug : Jet S (Fin d) m →ₐ[S] S) ≫ j m = 1)
    (hb : Function.Bijective (dif x0 (j 1) (h0 1))) : IsFormalParam G x0 j := by
  refine ⟨ht, h0, fun m B _ _ I hI g hg => ?_⟩
  have hp := isGrpPullback_pullback G x0
  have hG' : Smooth ((Over.pullback x0).obj G).hom :=
    smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) hG
  let P : ∀ (A : Type) [CommRing A] [Algebra S A],
      (Chart.sp (R₀ := S) A ⟶ (Over.pullback x0).obj G) →* (overAt x0 A ⟶ G) := fun A _ _ => pushHom hp (Chart.sp A)
  have inj : ∀ (A : Type) [CommRing A] [Algebra S A], Function.Injective (P A) := fun A _ _ u v h =>
    Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) h) ((Over.w u).trans (Over.w v).symm))
  have sur : ∀ (A : Type) [CommRing A] [Algebra S A], Function.Surjective (P A) := fun A _ _ w =>
    ⟨Over.homMk (pullback.lift w.left _ (Over.w w)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have nat : ∀ {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (f : A →ₐ[S] A') y,
      P A' (Chart.spMap f ≫ y) = homAt x0 f ≫ P A y := fun f y => Over.OverMorphism.ext (Category.assoc _ _ _)
  choose x hx using fun m => sur (Jet S (Fin d) m) (j m)
  let x' : ∀ m : ℕ, Chart.sp (R₀ := S) (Chart.JetR S (Fin d) m) ⟶ (Over.pullback x0).obj G := x
  have dl : ∀ c : Fin d → S, P _ (Chart.spMap (Chart.dualLift c) ≫ x' 1) = tv (dif x0 (j 1) (h0 1) c) := fun c => by
    have e : (Chart.dualLift c : Jet S (Fin d) 1 →ₐ[S] DualNumber S) = jetVec c :=
      jext fun i => (Chart.dualLift_zR c i).trans (jetVec_z_one c i).symm
    refine (congrArg (fun f : Jet S (Fin d) 1 →ₐ[S] DualNumber S => P _ (Chart.spMap f ≫ x 1)) e).trans ?_
    rw [nat, hx, tv_dif]
  let v : Fin d → (epsR S ⟶ (Over.pullback x0).obj G) := fun i => Chart.spMap (Chart.dualLift (Pi.single i 1)) ≫ x' 1
  have pr : ∀ c : Fin d → S, P _ (Chart.prodPts c v) = tv (dif x0 (j 1) (h0 1) c) := fun c => by
    have e : c = ∑ i, c i • (Pi.single i 1 : Fin d → S) := by
      funext k; simp [Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [e, map_sum]
    simp only [map_smul]
    rw [tv_comb, Chart.prodPts, List.prod_ofFn, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [nat, ← dl]
    rfl
  have tan : ∀ w : Chart.sp (R₀ := S) (DualNumber S) ⟶ (Over.pullback x0).obj G,
      Chart.IsTan w ↔ smT x0 0 (P _ w) = 1 := fun w => by
    constructor
    · intro hw
      have := congrArg (P _) (Chart.spMap_scaleD_zero hw)
      rwa [nat, map_one] at this
    · intro hw
      apply inj
      rw [nat, map_one]
      refine tan_pull x0 _ ?_ _ hw
      rw [homAt_comp]
      congr 1
      exact AlgHom.ext fun r => by simp
  have hv : IsLieBasis v := by
    refine ⟨fun i => (Chart.isTan_iff _).1 ((tan _).2 ?_), fun w hw => ?_⟩
    · rw [dl]; exact tv_zero' _
    · have hw' := (tan w).1 ((Chart.isTan_iff _).2 hw)
      obtain ⟨c, hc, hu⟩ := hb.existsUnique (mkT _ hw')
      refine ⟨c, (Chart.isLieComb_iff _ _ _).2 (inj _ ?_), fun c' hc' => hu c' (tv_injective ?_)⟩
      · rw [pr, hc]; rfl
      · rw [← pr, ← (Chart.isLieComb_iff _ _ _).1 hc']; rfl
  have h₁ : ∀ m, Chart.spMap (Chart.jetTruncR S (Fin d) m) ≫ x' (m + 1) = x' m := fun m => inj (Jet S (Fin d) m) (by
    refine (nat (A := Jet S (Fin d) (m + 1)) (A' := Jet S (Fin d) m) jetTrunc (x (m + 1))).trans ?_
    rw [hx, ht]; exact (hx m).symm)
  have h₂ : ∀ m, Chart.spMap (Chart.jetZeroR S (Fin d) m) ≫ x' m = 1 := fun m => inj (Jet S (Fin d) 0) (by
    have e : (Algebra.ofId S (Jet S (Fin d) 0)).comp (jetAug : Jet S (Fin d) m →ₐ[S] S) =
        Chart.jetZeroR S (Fin d) m :=
      jext fun i => by
        rw [AlgHom.comp_apply, jetAug_z, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact X_mem_orig i)).symm
    refine (congrArg (fun f : Jet S (Fin d) m →ₐ[S] Jet S (Fin d) 0 => P _ (Chart.spMap f ≫ x m)) e.symm).trans ?_
    rw [nat, hx, ← hcomp, h0, MonObj.comp_one]
    exact (map_one _).symm)
  obtain ⟨g', rfl⟩ := sur B g
  obtain ⟨ψ, hψ, hu⟩ := NilChart.existsUnique_coord hG' hv h₁ h₂ (fun _ => rfl) hI g'
    (inj _ (by rw [nat, map_one]; exact hg))
  have tr : ∀ f : Jet S (Fin d) m →ₐ[S] B, algMap x0 f ≫ j m = P B (Chart.spMap f ≫ x m) := fun f => by
    rw [nat, hx]; rfl
  exact ⟨ψ, (tr ψ).trans (congrArg _ hψ), fun f hf => hu f (inj _ ((tr f).symm.trans hf))⟩

end Param

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {d : ℕ} {κ : Type} [Fintype κ]

def IsTanBasisG (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) : Prop :=
  (∀ ℓ, IsTanAtG t x0 (tg ℓ)) ∧ ∀ w, IsTanAtG t x0 w → ∃! a : κ → S, IsCombAtG t x0 (m := Fintype.card κ)
    (fun i => tg ((Fintype.equivFin κ).symm i)) (fun i => a ((Fintype.equivFin κ).symm i)) w

variable (j : JetPts t.G x0 d)

theorem zero_iff (m : ℕ) :
    homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ famEquiv x0 t.G d j m = 1 ↔
      algMap x0 (jetAug : Jet S (Fin d) m →ₐ[S] S) ≫ j m = 1 := by
  rw [famEquiv_apply, hcomp, aug_jIn, algMap_eq]

theorem trunc_iff (m : ℕ) :
    homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ famEquiv x0 t.G d j (m + 1) =
        famEquiv x0 t.G d j m ↔
      algMap x0 (jetTrunc : Jet S (Fin d) (m + 1) →ₐ[S] Jet S (Fin d) m) ≫ j (m + 1) = j m := by
  rw [famEquiv_apply, famEquiv_apply, hcomp, trunc_jIn, ← hcomp, algMap_eq]
  exact ⟨jIn_cancel x0, fun h => by rw [h]⟩

theorem comb_iff_sum {σ : Type} [Fintype σ] {n : ℕ} (e : Fin n ≃ σ) (U : σ → TanM x0 t.G) (a : σ → S)
    (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x0 (fun i => (tv (U (e i))).left) (fun i => a (e i)) w ↔ (tv (∑ ℓ, a ℓ • U ℓ)).left = w := by
  rw [isCombAtG_iff t x0 (fun i => tv (U (e i))), tv_comb, ← Equiv.prod_comp e]
  rfl

theorem tan_iff (h0 : algMap x0 (jetAug : Jet S (Fin d) 1 →ₐ[S] S) ≫ j 1 = 1)
    (v : Sp (DualNumber S) ⟶ t.G.left) (c : Fin d → S) :
    TanIs t.G x0 j v c ↔ IsCombAtG t x0 (fun i : Fin d => (homAt x0
      (jetTan ((0 : Fin 1), i) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ famEquiv x0 t.G d j 1).left) c v := by
  have e₁ : ∀ i : Fin d, homAt x0 (jetTan ((0 : Fin 1), i) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫
      famEquiv x0 t.G d j 1 = tv (dif x0 (j 1) h0 (Pi.single i 1)) := fun i => by
    refine Eq.trans ?_ (tv_dif x0 _ _ _).symm
    rw [← tan_jIn, ← hcomp]; rfl
  have e₂ : ∑ i, c i • dif x0 (j 1) h0 (Pi.single i 1) = dif x0 (j 1) h0 c := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum]
    congr 1
    funext k; simp [Pi.single_apply]
  simp only [e₁]
  refine Iff.trans ?_ (comb_iff_sum t x0 (Equiv.refl _) (fun i => dif x0 (j 1) h0 (Pi.single i 1)) c v).symm
  rw [e₂]
  exact eq_comm

end Main

section Framed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {d : ℕ}

end Framed

end GlobalTheory.ChartCompare
