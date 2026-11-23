module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPolynomialEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelOfTheta

open GlobalTheory.CechPic

section Algebra

variable {G U : Type} [CommGroup G] [CommGroup U]

end Algebra

section Classes

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

theorem pull_one (hL : L.IsLB) (hr : Out.Rigidified A L) (T : Over S) :
    pull (1 : T ⟶ A).left (cls L hL) = 0 := by
  have e : pull (eSec A) (cls L hL) = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 hr
  have e' : (1 : T ⟶ A).left = (toUnit T).left ≫ eSec A := rfl
  rw [e', pull_comp, e, map_zero]

omit [GrpObj A] in
theorem pull_pull {T T' : Over S} (f : T' ⟶ T) (a : T ⟶ A) (c : Pic A.left) :
    pull f.left (pull a.left c) = pull (f ≫ a).left c := (pull_comp _ _ _).symm

variable [IsCommMonObj A]

theorem isLB_lam (hL : L.IsLB) : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _

theorem cls_lam (hL : L.IsLB) :
    cls _ (isLB_lam hL) = pull (fst A A * snd A A).left (cls L hL) - pull (fst A A).left (cls L hL) -
      pull (snd A A).left (cls L hL) + pull (1 : A ⊗ A ⟶ A).left (cls L hL) := by
  refine (cls_linComb hL _ _ (isLB_lam hL)).trans ?_
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum A (x2 A) I).left (cls L hL)) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have p₀ : psum A (x2 A) ∅ = 1 := rfl
  have p₁ : psum A (x2 A) {0} = fst A A := _root_.mul_one (fst A A)
  have p₂ : psum A (x2 A) {1} = snd A A := _root_.mul_one (snd A A)
  have p₃ : psum A (x2 A) {0, 1} = fst A A * snd A A := congrArg (fst A A * ·) (_root_.mul_one (snd A A))
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [neg_smul, one_smul]
  abel

theorem pull_lam (hL : L.IsLB) (hr : Out.Rigidified A L) {T : Over S} (a b : T ⟶ A) :
    pull (lift a b).left (cls _ (isLB_lam hL)) =
      pull (a * b).left (cls L hL) - pull a.left (cls L hL) - pull b.left (cls L hL) := by
  rw [cls_lam hL, pull_one hL hr, add_zero, map_sub, map_sub, pull_pull, pull_pull, pull_pull, MonObj.comp_mul,
    lift_fst, lift_snd]

end Classes

section Pairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L M : LB A.left}

theorem exists_theta_iff (hL : L.IsLB) (k : ℤ) {T : Over S} (x : T ⟶ A) :
    (∃ θ : Out.ThetaGrp A L k T, θ.pt = x) ↔
      k • pull (snd T A).left (cls L hL) - k • pull (Out.translPt A x).left (cls L hL) = 0 := by
  have e := cls_linComb hL (K := Fin 2) ![(snd T A).left, (Out.translPt A x).left] ![k, -k] (LB.isLB_linComb hL _ _)
  rw [Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, ← sub_eq_add_neg] at e
  rw [← e, cls_eq_zero_iff]
  exact ⟨fun ⟨θ, h⟩ => h ▸ ⟨θ.φ, θ.isGen⟩, fun ⟨t, ht⟩ => ⟨⟨x, t, ht⟩, rfl⟩⟩

theorem weilIs_of_pow (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (hM : M.IsLB) (d : ℕ)
    (e : cls M hM = d • cls L hL) {k : ℤ} {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs A L k x y c) : Out.WeilIs A M k x y (c ^ d) := by
  have up : ∀ (T' : Over S) (u : T' ⟶ A), (∃ θ : Out.ThetaGrp A L k T', θ.pt = u) →
      ∃ θ : Out.ThetaGrp A M k T', θ.pt = u := fun T' u H => by
    rw [exists_theta_iff hL] at H
    rw [exists_theta_iff hM, e, map_nsmul, map_nsmul, smul_comm k d, smul_comm k d, ← smul_sub, H, smul_zero]
  obtain ⟨c', hc'⟩ := CommutatorPairing.exists_weilIs (k := k) (x := x) (y := y) hG hA hM
    (fun p => by
      obtain ⟨V, hV, ⟨θ, -, H, -⟩, -⟩ := h p
      exact ⟨V, hV, up _ _ ⟨θ, H⟩⟩)
    (fun p => by
      obtain ⟨V, hV, ⟨-, θ, -, H⟩, -⟩ := h p
      exact ⟨V, hV, up _ _ ⟨θ, H⟩⟩)
  have iso : LBIso (lbPow L d) (M.pull (𝟙 A : A ⟶ A).left) :=
    (cls_eq_iff (isLB_lbPow hL d) (pull_isLB hM _)).1 (by
      rw [cls_lbPow hL, cls_pull hM, Over.id_left, pull_id, e])
  have := (weilIs_along_hom hG S A A (𝟙 A) L M d k T x y c c' hA hA hL hM inferInstance iso
    (by simpa using hc')).2 h
  exact this ▸ hc'

end Pairing

section Principal

variable {S : Scheme.{0}}

theorem cls_diag (hG : Out.GlobalFnsSt)
    (hc : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    (P : Out.PolAV S) [IsCommMonObj P.A] :
    cls _ (pull_isLB (isLB_lam P.isLB) (lift (𝟙 P.A) (𝟙 P.A)).left) = 2 • cls P.L P.isLB := by
  have h := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2
    ((MulPull.mulPull_of_cube_of_symm hc (exists_gen_negLB hG)).1 S P 2)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id] at h
  have e : Out.mulA P.A 2 = 𝟙 P.A * 𝟙 P.A := pow_two _
  rw [e] at h
  rw [cls_pull (isLB_lam P.isLB), pull_lam P.isLB P.rigid, Over.id_left, pull_id]
  rw [← sub_eq_zero, ← neg_eq_zero, ← h]
  push_cast
  module

theorem relAmple_of_pow {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) (h : Out.RelAmple A L) : Out.RelAmple A M := by
  have := hA.proper
  rw [relAmple_iff_isAmpleLB A hL] at h
  refine relAmple_of_isAmpleLB A hM fun U hU => ?_
  refine (isAmpleLB_congr (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _) ((cls_eq_iff (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)).1 ?_)).1
    ((isAmpleLB_pow_iff (pull_isLB hL _) hd).2 (h U hU))
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

end Principal

section Level

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

end Level

end GlobalTheory.SiegelOfTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TautologicalModel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Proof.TautologicalModel

section Taut

variable {X X' Y Z : Scheme.{0}}

theorem taut_le (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') (J : PUnit → L.ι) (K : PUnit → PUnit → L.ι) :
    (L.pull (p ≫ F)).U J ⊓ ((L.pull F).pull p).U K ≤ (p ≫ F) ⁻¹ᵁ (L.U (J ⟨⟩) ⊓ L.U (K ⟨⟩ ⟨⟩)) := fun _ hy =>
  ⟨mem_pull.1 hy.1, mem_pull (L := L) (F := F).1 (mem_pull (L := L.pull F) (F := p).1 hy.2)⟩

def taut (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') : LB.Iso ((L.pull F).pull p) (L.pull (p ≫ F)) :=
  ⟨fun q => res (taut_le L F p q.1 q.2) (pullU (p ≫ F) _ (L.g (q.1 ⟨⟩) (q.2 ⟨⟩ ⟨⟩)))⟩

theorem gw_taut (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') (f : Z ⟶ Y) (z : Z) (j : L.ι) (k : PUnit → PUnit → L.ι)
    (hj : (p ≫ F) (f z) ∈ L.U j) (hk : f z ∈ ((L.pull F).pull p).U k) :
    gw (taut L F p) f z j k = gm (f ≫ p ≫ F) z _ (L.g j (k ⟨⟩ ⟨⟩)) := by
  have hm : f z ∈ (L.pull (p ≫ F)).U (fun _ => j) ⊓ ((L.pull F).pull p).U k := ⟨mem_pull.2 hj, hk⟩
  exact (gm_res f z (taut_le L F p _ k) hm _).trans (gm_pull f (p ≫ F) z _ (taut_le L F p _ k hm) _)

theorem taut_isGen {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) (p : Y ⟶ X') : (taut L F p).IsGen := by
  refine (isGen_iff _).2 fun Z f z j j' k k' hj hj' hk hk' => ?_
  have h1 : (f ≫ p) z ∈ (L.pull F).U (k ⟨⟩) := mem_pull (L := L.pull F) (F := p).1 hk
  have h1' : (f ≫ p) z ∈ (L.pull F).U (k' ⟨⟩) := mem_pull (L := L.pull F) (F := p).1 hk'
  have h2 : (f ≫ p ≫ F) z ∈ L.U (k ⟨⟩ ⟨⟩) := mem_pull (L := L) (F := F).1 h1
  have h2' : (f ≫ p ≫ F) z ∈ L.U (k' ⟨⟩ ⟨⟩) := mem_pull (L := L) (F := F).1 h1'
  rw [gw_taut L F p f z j k hj hk, gw_taut L F p f z j' k' hj' hk', gm_pull_g (L.pull F) p f z k k' hk hk',
    gm_pull_g L F (f ≫ p) z _ _ h1 h1', Category.assoc,
    ← gm_cocycle hL (f ≫ p ≫ F) z (i := j) (j := j') hj hj' h2,
    ← gm_cocycle hL (f ≫ p ≫ F) z (i := j') (j := k ⟨⟩ ⟨⟩) hj' h2 h2']
  generalize gm (f ≫ p ≫ F) z _ (L.g j j') = A
  generalize gm (f ≫ p ≫ F) z _ (L.g j' (k ⟨⟩ ⟨⟩)) = B
  generalize gm (f ≫ p ≫ F) z _ (L.g (k ⟨⟩ ⟨⟩) (k' ⟨⟩ ⟨⟩)) = C
  rw [_root_.mul_comm B C, _root_.mul_assoc, inv_mul_cancel_left]

end Taut

section Rig

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]

theorem gm_rigPullOf (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) {Z : Scheme.{0}}
    (f : Z ⟶ (𝟙_ (Over S')).left) (z : Z) (j : PUnit → PUnit → L.ι)
    (hj : f z ∈ LB.wchart (L.pull F) (fun _ : PUnit => eSec G') j) :
    gm f z (LB.wchart (L.pull F) (fun _ : PUnit => eSec G') j) ((rigPullOf F e he L r).s j) =
      gm (f ≫ e) z (LB.wchart L (fun _ : PUnit => eSec G) (fun _ => j ⟨⟩ ⟨⟩)) (r.s (fun _ => j ⟨⟩ ⟨⟩)) :=
  (gm_res f z (rigPull_le F e he L j) hj _).trans (gm_pull f e z _ (rigPull_le F e he L j hj) _)

theorem rigPullOf_isGen (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) (hr : r.IsGen) :
    (rigPullOf F e he L r).IsGen := by
  intro i j
  refine unit_ext fun y hy => ?_
  have hi' := rigPull_le F e he L i hy.1
  have hj' := rigPull_le F e he L j hy.2
  refine ((gm_res _ y _ hy _).trans (gm_rigPullOf F e he L r (𝟙 _) y i hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g (L.pull F) (eSec G') (𝟙 _) y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans (gm_rigPullOf F e he L r (𝟙 _) y j hy.2)))).trans ?_
  rw [gen_trans (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) hr (𝟙 _ ≫ e) y hi' hj', trF, Fintype.prod_unique,
    zpow_one, gm_pull_g L F (𝟙 _ ≫ eSec G') y (i ⟨⟩) (j ⟨⟩) (mem_pull (L := L.pull F) (F := eSec G').1 hy.1)
      (mem_pull (L := L.pull F) (F := eSec G').1 hy.2), Category.assoc, Category.assoc, he]

end Rig

end GlobalTheory.Proof.TautologicalModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealPrimeAvoidingVariable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory.ThetaPrime

theorem eval₂_smul_of_isHomogeneous {o K I : Type} [CommRing o] [CommRing K] (β : o →+* K)
    (v : I → K) (c : K) {F : MvPolynomial I o} {n : ℕ} (hF : F.IsHomogeneous n) :
    MvPolynomial.eval₂ β (c • v) F = c ^ n * MvPolynomial.eval₂ β v F := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∑ i ∈ m.support, m i = n := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, h1]
  ring

theorem exists_homogenisation {o I D : Type} [CommRing o] (a₀ : I) (a : D → I)
    (G : MvPolynomial D o) : ∃ (n : ℕ) (H : MvPolynomial I o),
      ∀ (K : Type) [Field K] (β : o →+* K) (v : I → K), v a₀ ≠ 0 →
        MvPolynomial.eval₂ β v H = v a₀ ^ n * MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G := by
  induction G using MvPolynomial.induction_on with
  | C c => exact ⟨0, MvPolynomial.C c, fun K _ β v _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨n, H, hH⟩ := hp
    obtain ⟨m, H', hH'⟩ := hq
    refine ⟨n + m, MvPolynomial.X a₀ ^ m * H + MvPolynomial.X a₀ ^ n * H', fun K _ β v hv => ?_⟩
    simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
      MvPolynomial.eval₂_X, hH K β v hv, hH' K β v hv]
    ring
  | mul_X p i hp =>
    obtain ⟨n, H, hH⟩ := hp
    refine ⟨n + 1, H * MvPolynomial.X (a i), fun K _ β v hv => ?_⟩
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, hH K β v hv]
    field_simp
    ring

noncomputable def coneIdeal {o I Z : Type} [CommRing o] (em : o →+* ℂ) (B : Set Z) (θ : Z → I → ℂ) :
    Ideal (MvPolynomial I o) :=
  ⨅ (z : Z) (_ : z ∈ B) (c : ℂ) (_ : c ≠ 0), RingHom.ker (MvPolynomial.eval₂Hom em (c • θ z))

theorem mem_coneIdeal {o I Z : Type} [CommRing o] {em : o →+* ℂ} {B : Set Z} {θ : Z → I → ℂ}
    {F : MvPolynomial I o} : F ∈ coneIdeal em B θ ↔
      ∀ z ∈ B, ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval₂ em (c • θ z) F = 0 := by
  simp [coneIdeal, Ideal.mem_iInf, RingHom.mem_ker]

theorem coneIdeal_isPrime {o I : Type} [CommRing o] [Countable o] [Countable I] (em : o →+* ℂ)
    {d : ℕ} {B : Set (Fin d → ℂ)} (θ : (Fin d → ℂ) → I → ℂ) (ho : IsOpen B)
    (hc : IsPreconnected B) (hn : B.Nonempty) (hd : ∀ a, DifferentiableOn ℂ (fun z => θ z a) B) :
    (coneIdeal em B θ).IsPrime := by
  obtain ⟨z, hz, c, hc0, h⟩ :=
    GlobalTheory.exists_veryGeneral_point_of_holomorphic_family o em I d B θ ho hc hn hd
  have : coneIdeal em B θ = RingHom.ker (MvPolynomial.eval₂Hom em (c • θ z)) := by
    ext F
    rw [mem_coneIdeal, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom]
    exact ⟨fun hF => hF z hz c hc0, h F⟩
  rw [this]
  exact RingHom.ker_isPrime _

theorem exists_ratios {o I : Type} [CommRing o] [Finite I] (em : o →+* ℂ)
    (hem : Function.Injective em) {d : ℕ} {B : Set (Fin d → ℂ)} (θ : (Fin d → ℂ) → I → ℂ)
    (ho : IsOpen B) (hd : ∀ a, DifferentiableOn ℂ (fun z => θ z a) B)
    (hf : ∀ z ∈ B, {z' ∈ B | ∃ c : ℂ, θ z' = c • θ z}.Countable) (a₁ : I)
    (h₁ : MvPolynomial.X a₁ ∉ coneIdeal em B θ) :
    ∃ (a₀ : I) (a : Fin d → I), MvPolynomial.X a₀ ∉ coneIdeal em B θ ∧
      ∀ (K : Type) [Field K] (β : o →+* K) (v : I → K),
        RingHom.ker (MvPolynomial.eval₂Hom β v) = coneIdeal em B θ →
        ∀ G : MvPolynomial (Fin d) o, MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G = 0 →
          G = 0 := by
  rw [mem_coneIdeal] at h₁
  push Not at h₁
  obtain ⟨z₁, hz₁, c₁, -, h₁⟩ := h₁
  have h₁' : θ z₁ a₁ ≠ 0 := by
    intro h
    apply h₁
    simp [h]
  have hcont : ContinuousAt (fun z => θ z a₁) z₁ :=
    (hd a₁).continuousOn.continuousAt (ho.mem_nhds hz₁)
  have hU : {z | z ∈ B ∧ θ z a₁ ≠ 0} ∈ nhds z₁ :=
    Filter.inter_mem (ho.mem_nhds hz₁) (hcont.eventually_ne h₁')
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hsub : Metric.ball z₁ ε ⊆ B := fun z hz => (hball hz).1
  obtain ⟨a₀, a, ⟨z₀, hz₀, h₀⟩, hind⟩ := GlobalTheory.CountableFibres.exists_independent_ratios d I
    (Metric.ball z₁ ε) θ Metric.isOpen_ball (convex_ball z₁ ε).isPreconnected
    ⟨z₁, Metric.mem_ball_self hε⟩ (fun a => (hd a).mono hsub)
    (fun z hz => ⟨fun h => (hball hz).2 (by rw [h]; rfl),
      Set.Countable.mono (fun z' hz' => And.intro (hsub hz'.1) hz'.2) (hf z (hsub hz))⟩)
  have hX : MvPolynomial.X a₀ ∉ coneIdeal em B θ := by
    intro h
    have := mem_coneIdeal.1 h z₀ (hsub hz₀) 1 one_ne_zero
    simp [h₀] at this
  refine ⟨a₀, a, hX, fun K _ β v hv G hG => ?_⟩
  have hv₀ : v a₀ ≠ 0 := by
    intro h
    apply hX
    rw [← hv, RingHom.mem_ker]
    simp [h]
  obtain ⟨n, H, hH⟩ := exists_homogenisation a₀ a G
  have hHP : H ∈ coneIdeal em B θ := by
    rw [← hv, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, hH K β v hv₀, hG, mul_zero]
  have hmap : MvPolynomial.map em G = 0 := by
    refine hind _ fun z hz hz0 => ?_
    have := mem_coneIdeal.1 hHP z (hsub hz) 1 one_ne_zero
    rw [one_smul, hH ℂ em _ hz0] at this
    rw [MvPolynomial.eval_map]
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hz0)
  exact MvPolynomial.map_injective em hem (by rw [hmap, map_zero])

theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) :
    Countable o := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have : Countable (MvPolynomial (Fin n) ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans (by simp)
  exact hf.countable

theorem span_range_eq_top {K I : Type} [Field K] {v : I → K} (hv : v ≠ 0) :
    Ideal.span (Set.range v) = ⊤ := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hv
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a, rfl⟩) (IsUnit.mk0 _ ha)

theorem exists_prime_independent_ratios : Out.Laws → Out.Laws2 → ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (p : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₁ : Ix g (N' ^ 2)), N' ≠ 0 → p.IsPrime → thIdeal em C ≤ p → MvPolynomial.X a₁ ∉ p → ∃ (P : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₀ : Ix g (N' ^ 2)) (a : Fin d → Ix g (N' ^ 2)), P.IsPrime ∧ thIdeal em C ≤ P ∧ P ≤ p ∧ MvPolynomial.X a₀ ∉ P ∧ ∀ (K : Type) [Field K] (β : o →+* K) (v : Ix g (N' ^ 2) → K), RingHom.ker (MvPolynomial.eval₂Hom β v) = P → ∀ G : MvPolynomial (Fin d) o, MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G = 0 → G = 0 := by
  intro hL hL2 g N' J Mat κ w w' o _ b em C d hAr hG p a₁ hN hp hle hX
  obtain ⟨-, hft, hem⟩ := hAr
  have : Countable o := countable_of_finiteType o hft
  have : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN⟩
  obtain ⟨r, B, θ, hfam, hcov⟩ := hG.fam
  have hmem : ∀ F, F ∈ thIdeal em C ↔ ∀ t v, C t → t.HasTh (𝟙 _) v →
      MvPolynomial.eval₂ em v F = 0 := by
    intro F
    simp [thIdeal, Ideal.mem_iInf, RingHom.mem_ker]
  have hinf : (Finset.univ : Finset (Fin r)).inf (fun i => coneIdeal em (B i) (θ i)) ≤ p := by
    refine le_trans (fun F hF => ?_) hle
    rw [hmem]
    intro t v ht hv
    obtain ⟨i, z, hz, hθ⟩ := hcov t ht
    have hFi : F ∈ coneIdeal em (B i) (θ i) :=
      (Finset.inf_le (f := fun i => coneIdeal em (B i) (θ i)) (Finset.mem_univ i)) hF
    have key : ∃ c : ℂ, c ≠ 0 ∧ v = c • θ i z := by
      by_cases h0 : θ i z = 0
      · refine ⟨1, one_ne_zero, ?_⟩
        by_contra hne
        rw [h0, smul_zero] at hne
        obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t ℂ _ v (θ i z) hv hθ
          (span_range_eq_top hne)
        apply hne
        funext a
        have := hu a
        rw [h0] at this
        simpa using this
      · obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t ℂ _ (θ i z) v hθ hv
          (span_range_eq_top h0)
        exact ⟨u, u.ne_zero, funext hu⟩
    obtain ⟨c, hc, rfl⟩ := key
    exact mem_coneIdeal.1 hFi z hz c hc
  obtain ⟨i, -, hi⟩ := hp.inf_le'.1 hinf
  obtain ⟨ho, hc, hd, hz⟩ := hfam i
  have hX' : MvPolynomial.X a₁ ∉ coneIdeal em (B i) (θ i) := fun h => hX (hi h)
  have hn : (B i).Nonempty := by
    by_contra hne
    apply hX'
    rw [mem_coneIdeal]
    intro z hz
    exact absurd ⟨z, hz⟩ hne
  obtain ⟨a₀, a, h₀, hind⟩ := exists_ratios em hem (θ i) ho hd (fun z hz' => (hz z hz').2) a₁ hX'
  refine ⟨_, a₀, a, coneIdeal_isPrime em (θ i) ho hc hn hd, fun F hF => ?_, hi, h₀, hind⟩
  rw [mem_coneIdeal]
  intro z hz' c _
  obtain ⟨t, ht, hθ⟩ := (hz z hz').1
  have hcomp := (GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g N' J b em C hem).2.1 F hF
  rw [← MvPolynomial.sum_homogeneousComponent F, MvPolynomial.eval₂_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [eval₂_smul_of_isHomogeneous em _ c (MvPolynomial.homogeneousComponent_isHomogeneous e F),
    (hmem _).1 (hcomp e) t _ ht hθ, mul_zero]

end GlobalTheory.ThetaPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaObjectConstantFamilyDualNumbersIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

namespace GlobalTheory.KS
private theorem k_ne_zero_lemma {o : Type} [CommRing o] {k : ℕ} (b : TBase o k) (s₀ : Sp ℂ ⟶ Sp o) :
    k ≠ 0 := by
  rintro rfl
  have h0 : (0 : o) = 1 := isUnit_zero_iff.mp (by simpa using b.unit)
  haveI : Subsingleton o := subsingleton_of_zero_eq_one h0
  obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum ℂ))
  exact (s₀.base x).isPrime.ne_top (Subsingleton.elim _ _)

theorem tMap_of_isConst : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (s₀ : Sp ℂ ⟶ Sp o) (s' : Sp (DualNumber ℂ) ⟶ Sp o) (t₀ : TObj g k J b s₀) (t' : TObj g k J b s') (ρ : t'.A.left ⟶ t₀.A.left) (j : t₀.A.left ⟶ t'.A.left), IsConst t'.A t₀.A ρ j → (IsGrpPullback t₀.A t'.A (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j ∧ LBIso t₀.L (t'.L.pull j) ∧ (∀ i, (t₀.pt i).left ≫ j = (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (t'.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ j = j ≫ (t'.act jj).left) → TMap t' t₀ (spMap (algebraMap ℂ (DualNumber ℂ))) := by
  intro hL hL2 hT o _ g k J b s₀ s' t₀ t' ρ j hc ⟨hpb, hlb, hpt, hact⟩
  have hk : k ≠ 0 := k_ne_zero_lemma b s₀
  refine ⟨ρ, hc.1, ?_, ?_, ?_⟩
  · obtain ⟨u, Hm, χ, hu, -⟩ := GlobalTheory.KSInh.exists_goodU_ksRel hT t₀.pol
    exact GlobalTheory.SymRigid.lbIso_pull_of_isConst hL t₀.pol u Hm χ hu t'.A ρ j hc t'.L t'.isLB t'.sym hlb
  · intro i
    exact _root_.GlobalTheory.KS.torsion_section_const hL t₀.pol t'.A ρ j hc k (t'.pt i) (t₀.pt i) hk (t'.torsion i) (t₀.torsion i) (hpt i).symm
  · intro jj
    exact _root_.GlobalTheory.ConstEndo.endo_comp_proj hL hL2 t₀.pol t'.A ρ j hc (t'.act jj) (t₀.act jj) t'.ab (t'.hom jj) (t₀.hom jj) (hact jj).symm
end GlobalTheory.KS
end

