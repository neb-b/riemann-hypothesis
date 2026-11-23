module

public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.InterpolationHolds
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0009
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.CoefProd

@[expose] public section

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.Bridge
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems Formalism.MainNotions.FormalGroupSystem.Pf

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

abbrev GlobalTheory : Type := Σ v : Fin P.nV, Fin (P.n' v)

def emP (b : GlobalTheory P) (v : Fin (P.m + 1) × Fin (P.m + 1)) :
    (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) := ⟨b.1, (b.2, v)⟩

def gam (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (b : GlobalTheory P) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf :=
  la_tw (P.ι b.1) (P.σ b.1) b.2.val (g b.1)

def nuB (b : GlobalTheory P) : Fin (P.m + 1) → ℕ := nuOf (lamAt (P.lam0 b.1) b.2)

def eB (b : GlobalTheory P) : ℤ := lamAt (P.lam0 b.1) b.2 (Fin.last P.m)

def sB (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) : Kf := ∏ b : GlobalTheory P, (gam P g b).det ^ (-(eB P b))

theorem prod_blocks (c : GlobalTheory P → Kf) (F : GlobalTheory P → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf) :
    ∏ v, P.vEmb v (∏ s, blockEmb Kf s (c ⟨v, s⟩ • F ⟨v, s⟩)) = (∏ b, c b) • ∏ b, rename (emP P b) (F b) := by
  have e1 : ∀ (b : GlobalTheory P) (G : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf),
      P.vEmb b.1 (blockEmb Kf b.2 G) = rename (emP P b) G := by
    intro b G
    simp only [Places.vEmb, blockEmb]
    rw [rename_rename]
    rfl
  rw [show (∏ b, c b) • ∏ b, rename (emP P b) (F b) = ∏ b : GlobalTheory P, c b • rename (emP P b) (F b) by
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]]
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_smul, map_smul, e1 ⟨v, s⟩]

theorem delta_zero_eq_twisted_delta (hinj : Function.Injective (algebraMap O Kf)) (v : Fin P.nV) (s : Fin (P.n' v))
    (g : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (hg : IsUnit g.det) :
    Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) g)) =
      deltaLTw O Kf P.m (lamAt (P.lam0 v) s) (la_tw (P.ι v) (P.σ v) s.val g) := by
  have hd : Antitone (lamAt (P.lam0 v) s) := by
    unfold lamAt
    split_ifs
    · exact P.dom v s
    · intro i j hij
      exact neg_le_neg (P.dom v s (Fin.rev_le_rev.2 hij))
  rw [la_extO (P.ι v) (P.σ v) (P.j v)
    (fun x => by obtain ⟨y, hy⟩ := (P.setting v).frob x; exact ⟨_, hy⟩) (P.setting v).ι_comp s.val g]
  have hg' := la_tw_det (P.ι v) (P.σ v) s.val g hg
  refine le_antisymm (lowest_invariant_le_delta _ _ hd _ hg') ?_
  unfold Dl0
  rw [if_pos hd]
  refine le_iInf₂ fun h hh => ?_
  exact dl_indep O Kf hinj _ _ _ h hg' hh.2

variable (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (hg : ∀ v, IsUnit (g v).det)


include hg in
theorem htupW_le (hinj : Function.Injective (algebraMap O Kf)) (T : Submodule O P.Xsp)
    (hT : ∀ F : GlobalTheory P → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf,
      (∀ b, F b ∈ deltaL O Kf (P.m + 1) (nuB P b) (gam P g b)) → sB P g • ∏ b, rename (emP P b) (F b) ∈ T) :
    P.HtupW (fun v => colSpan (P.W v) (g v)) ≤ T := by
  have key : ∀ S : Fin P.nV → Set P.Xsp,
      (∀ f : Fin P.nV → P.Xsp, (∀ v, f v ∈ S v) → ∏ v, f v ∈ T) →
      ∀ f : Fin P.nV → P.Xsp, (∀ v, f v ∈ Submodule.span O (S v)) → ∏ v, f v ∈ T := by
    intro S h f hf
    classical
    suffices H : ∀ A : Finset (Fin P.nV), ∀ f : Fin P.nV → P.Xsp,
        (∀ i ∈ A, f i ∈ Submodule.span O (S i)) → (∀ i ∉ A, f i ∈ S i) → ∏ i, f i ∈ T from
      H Finset.univ f (fun i _ => hf i) (fun i hi => absurd (Finset.mem_univ i) hi)
    intro A
    refine Finset.induction_on A ?_ ?_
    · intro f _ h2
      exact h f (fun i => h2 i (by simp))
    · intro a A ha ih f h1 h2
      have hR : ∀ x ∈ Submodule.span O (S a), x * ∏ j ∈ Finset.univ \ {a}, f j ∈ T := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          have h3 := ih (Function.update f a y) (fun i hi => ?_) (fun i hi => ?_)
          · rwa [Finset.prod_update_of_mem (Finset.mem_univ a)] at h3
          · have hia : i ≠ a := by rintro rfl; exact ha hi
            simp only [Function.update_apply, hia, if_false]
            exact h1 i (Finset.mem_insert_of_mem hi)
          · by_cases hia : i = a
            · subst hia
              simp only [Function.update_apply, if_true]
              exact hy
            · simp only [Function.update_apply, hia, if_false]
              exact h2 i (by simp [hia, hi])
        | zero => rw [zero_mul]; exact T.zero_mem
        | add x y _ _ hx hy => rw [add_mul]; exact T.add_mem hx hy
        | smul c x _ hx => rw [smul_mul_assoc]; exact T.smul_mem c hx
      have h4 := Finset.prod_update_of_mem (Finset.mem_univ a) f (f a)
      rw [Function.update_eq_self] at h4
      rw [h4]
      exact hR _ (h1 a (Finset.mem_insert_self a A))
  unfold Places.HtupW Places.tenV
  rw [Submodule.span_le]
  rintro X ⟨F, hF, rfl⟩
  have hF' : ∀ v, P.vEmb v (F v) ∈ Submodule.span O
      (((P.vEmb v).toLinearMap.restrictScalars O) '' {Q | ∃ G : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf,
        (∀ s, G s ∈ deltaLTw O Kf P.m (lamAt (P.lam0 v) s) (la_tw (P.ι v) (P.σ v) s.val (g v))) ∧
          Q = ∏ s, blockEmb Kf s (G s)}) := by
    intro v
    rw [Submodule.span_image]
    refine Submodule.mem_map_of_mem ?_
    have h := hF v
    unfold HtenW tensorLat at h
    simp only [delta_zero_eq_twisted_delta P hinj v _ (g v) (hg v)] at h
    exact h
  refine key _ ?_ (fun v => P.vEmb v (F v)) hF'
  intro f hf
  choose Q hQ hfQ using hf
  choose G hG hQG using hQ
  have hG' : ∀ v s, ∃ H, H ∈ deltaL O Kf (P.m + 1) (nuB P ⟨v, s⟩) (gam P g ⟨v, s⟩) ∧
      (gam P g ⟨v, s⟩).det ^ (-(eB P ⟨v, s⟩)) • H = G v s := fun v s => Submodule.mem_map.1 (hG v s)
  choose H hH hHG using hG'
  have e : ∏ v, f v = sB P g • ∏ b : GlobalTheory P, rename (emP P b) (H b.1 b.2) := by
    rw [show sB P g • ∏ b : GlobalTheory P, rename (emP P b) (H b.1 b.2) = _ from
      (prod_blocks P (fun b => (gam P g b).det ^ (-(eB P b))) (fun b => H b.1 b.2)).symm]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← hfQ v, hQG v]
    show P.vEmb v _ = _
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← hHG v s]
  rw [e]
  exact hT (fun b => H b.1 b.2) (fun b => hH b.1 b.2)


include hg in
theorem mem_htupW (hinj : Function.Injective (algebraMap O Kf)) (F : GlobalTheory P → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf)
    (hF : ∀ b, F b ∈ deltaL O Kf (P.m + 1) (nuB P b) (gam P g b)) :
    sB P g • ∏ b, rename (emP P b) (F b) ∈ P.HtupW (fun v => colSpan (P.W v) (g v)) := by
  rw [show sB P g • ∏ b, rename (emP P b) (F b) = _ from
    (prod_blocks P (fun b => (gam P g b).det ^ (-(eB P b))) F).symm]
  unfold Places.HtupW Places.tenV
  apply Submodule.subset_span
  refine ⟨fun v => ∏ s, blockEmb Kf s ((gam P g ⟨v, s⟩).det ^ (-(eB P ⟨v, s⟩)) • F ⟨v, s⟩), fun v => ?_, rfl⟩
  unfold HtenW tensorLat
  apply Submodule.subset_span
  refine ⟨fun s => (gam P g ⟨v, s⟩).det ^ (-(eB P ⟨v, s⟩)) • F ⟨v, s⟩, fun s => ?_, rfl⟩
  show _ ∈ Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) (g v)))
  rw [delta_zero_eq_twisted_delta P hinj v s (g v) (hg v)]
  exact Submodule.mem_map.2 ⟨F ⟨v, s⟩, hF ⟨v, s⟩, rfl⟩

end Formalism.L2.PairingIndexBounds.Ent
end
end

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.CoefficientProductHolds
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.L2.G.Model.TS

section disjointProducts

variable {R B σ τ : Type*} [CommRing R] [Fintype B]

def dGlue (em : B → σ → τ) (p : B → σ →₀ ℕ) : τ →₀ ℕ :=
  ∑ b, (p b).mapDomain (em b)

lemma dGlue_apply (em : B → σ → τ) (hem : Function.Injective fun x : B × σ => em x.1 x.2)
    (p : B → σ →₀ ℕ) (b : B) (s : σ) : dGlue em p (em b s) = p b s := by
  classical
  unfold dGlue
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single b]
  · exact Finsupp.mapDomain_apply_of_injective (fun x y h => congrArg Prod.snd (hem (a₁ := (b, x)) (a₂ := (b, y)) h)) _ _
  · intro b' _ hb
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨w, hw⟩
    exact hb (congrArg Prod.fst (hem (a₁ := (b', w)) (a₂ := (b, s)) hw))
  · simp

lemma dGlue_injective (em : B → σ → τ) (hem : Function.Injective fun x : B × σ => em x.1 x.2) :
    Function.Injective (dGlue em) := fun p q h =>
  funext fun b => Finsupp.ext fun s => by rw [← dGlue_apply em hem p, h, dGlue_apply em hem]

lemma dGlue_fact (em : B → σ → τ) (hem : Function.Injective fun x : B × σ => em x.1 x.2)
    (p : B → σ →₀ ℕ) :
    ∏ x ∈ (dGlue em p).support, (dGlue em p x).factorial = ∏ b, ∏ v ∈ (p b).support, (p b v).factorial := by
  classical
  have key : ∀ t : Finset B, (∑ b ∈ t, (p b).mapDomain (em b)).prod (fun _ k => k.factorial) =
      ∏ b ∈ t, (p b).prod (fun _ k => k.factorial) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      have hinj : Function.Injective (em a) := fun x y h =>
        congrArg Prod.snd (hem (a₁ := (a, x)) (a₂ := (a, y)) h)
      have hd : Disjoint ((p a).mapDomain (em a)).support (∑ b ∈ t, (p b).mapDomain (em b)).support := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finsupp.mem_support_iff] at hx1 hx2
        obtain ⟨s, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hx1
        apply hx2
        rw [Finsupp.finsetSum_apply]
        refine Finset.sum_eq_zero fun b hb => ?_
        apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨w, hw⟩
        have hba : b = a := congrArg Prod.fst (hem (a₁ := (b, w)) (a₂ := (a, s)) hw)
        exact ha (hba ▸ hb)
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Finsupp.prod_add_index_of_disjoint hd, ih,
        Finsupp.prod_mapDomain_index_inj hinj]
  exact key Finset.univ

lemma rename_prod_expand [DecidableEq B] (em : B → σ → τ) (F : B → MvPolynomial σ R) :
    ∏ b, rename (em b) (F b) = ∑ p ∈ Fintype.piFinset (fun b => (F b).support),
      monomial (dGlue em p) (∏ b, AddMonoidAlgebra.coeff (F b) (p b)) := by
  calc ∏ b, rename (em b) (F b)
      = ∏ b, ∑ m ∈ (F b).support, rename (em b) (monomial m (AddMonoidAlgebra.coeff (F b) m)) := by
        refine Finset.prod_congr rfl fun b _ => ?_
        conv_lhs => rw [(F b).as_sum]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
    _ = ∑ p ∈ Fintype.piFinset (fun b => (F b).support),
          ∏ b, rename (em b) (monomial (p b) (AddMonoidAlgebra.coeff (F b) (p b))) := Finset.prod_univ_sum _ _
    _ = _ := Finset.sum_congr rfl fun p _ => by
        simp only [rename_monomial]
        exact prod_monomial_eq _ _ _

end disjointProducts

theorem fock_product_holds : FockProd := by
  intro K B σ τ _ _ em hem F G
  classical
  rw [rename_prod_expand em F, rename_prod_expand em G, fockR_sum_left]
  simp_rw [fockR_sum_right, fockR_expand (F _) (G _)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp_rw [fockR_monomial]
  by_cases h : p = q
  · subst h
    simp only [if_true, dGlue_fact em hem, Finset.prod_mul_distrib, Nat.cast_prod]
  · have h' : dGlue em p ≠ dGlue em q := fun e => h (dGlue_injective em hem e)
    rw [if_neg h']
    obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs)).symm

theorem coefficient_product_holds : CoefProd := by
  intro R B σ τ _ _ xm hxm H p
  classical
  rw [show (∑ b, (p b).mapDomain (xm b)) = dGlue xm p from rfl, rename_prod_expand xm H, coeff_sum]
  by_cases hp : p ∈ Fintype.piFinset fun b => (H b).support
  · rw [Finset.sum_eq_single p]
    · rw [coeff_monomial, if_pos rfl]
    · intro q _ hq
      rw [coeff_monomial, if_neg (fun e => hq (dGlue_injective xm hxm e))]
    · intro h; exact absurd hp h
  · rw [Finset.sum_eq_zero]
    · rw [Fintype.mem_piFinset] at hp
      push Not at hp
      obtain ⟨b, hb⟩ := hp
      exact (Finset.prod_eq_zero (Finset.mem_univ b) (notMem_support_iff.mp hb)).symm
    · intro q hq
      rw [coeff_monomial, if_neg]
      intro e
      exact hp (dGlue_injective xm hxm e ▸ hq)

end Formalism.L2.PairingIndexBounds.Ent
end
end

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.FockRSmulLeft
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.MainNotions.G

def cN (K : Type) [CommRing K] {n : ℕ} (ν : Fin n → ℕ) : K := fockR (hw K le_rfl ν) (hw K le_rfl ν)

theorem cN_ne (K : Type) [Field K] [CharZero K] {n : ℕ} (ν : Fin n → ℕ) : cN K ν ≠ 0 := by
  obtain ⟨N, hN, h⟩ := Top.hWNorm n n le_rfl ν
  unfold cN
  rw [h K]
  exact_mod_cast hN.ne'

theorem map_cN (K Kc : Type) [CommRing K] [CommRing Kc] (φ : K →+* Kc) {n : ℕ} (ν : Fin n → ℕ) : φ (cN K ν) = cN Kc ν := by
  obtain ⟨N, _, h⟩ := Top.hWNorm n n le_rfl ν
  unfold cN
  rw [h K, h Kc, map_natCast]

theorem fockR_add_left {σ R : Type} [CommRing R] (f f' g : MvPolynomial σ R) : fockR (f + f') g = fockR f g + fockR f' g :=
  (Top.fockRBilin σ R f f' g 0).1

theorem fockR_smul_left {σ R : Type} [CommRing R] (a : R) (f g : MvPolynomial σ R) : fockR (a • f) g = a * fockR f g :=
  (Top.fockRBilin σ R f 0 g a).2.1

theorem fockR_comm {σ R : Type} [CommRing R] (f g : MvPolynomial σ R) : fockR f g = fockR g f :=
  (Top.fockRBilin σ R f 0 g 0).2.2

theorem fockR_zero_left {σ R : Type} [CommRing R] (g : MvPolynomial σ R) : fockR 0 g = 0 := by
  have := fockR_smul_left (0 : R) (0 : MvPolynomial σ R) g
  rwa [zero_smul, zero_mul] at this

theorem fockR_sum_left {σ R ι : Type} [CommRing R] (s : Finset ι) (f : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR (∑ i ∈ s, f i) g = ∑ i ∈ s, fockR (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fockR_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fockR_add_left, ih]

def fockL {σ R : Type} [CommRing R] (g : MvPolynomial σ R) : MvPolynomial σ R →ₗ[R] R where
  toFun f := fockR f g
  map_add' f f' := fockR_add_left f f' g
  map_smul' a f := by rw [fockR_smul_left]; rfl

theorem rowAct_rowAct {R : Type} [CommRing R] {k n : ℕ} (g h : Matrix (Fin k) (Fin k) R) (F : MvPolynomial (Fin k × Fin n) R) :
    rowAct R g (rowAct R h F) = rowAct R (h * g) F :=
  congrArg (fun φ : MvPolynomial (Fin k × Fin n) R →ₐ[R] MvPolynomial (Fin k × Fin n) R => φ F) (rowActMul R k n g h)

theorem rowAct_one {R : Type} [CommRing R] {k n : ℕ} (F : MvPolynomial (Fin k × Fin n) R) : rowAct R (1 : Matrix (Fin k) (Fin k) R) F = F := by
  have : rowAct R (n := n) (1 : Matrix (Fin k) (Fin k) R) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    unfold rowAct
    rw [aeval_X]
    simp [Matrix.one_apply, ite_mul]
  rw [this]; rfl

theorem mem_deltaL' {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ} {ν : Fin n → ℕ} {g : Matrix (Fin n) (Fin n) K}
    {F : MvPolynomial (Fin n × Fin n) K} :
    F ∈ deltaL O K n ν g ↔ rowAct K g F ∈ (weyl O n n le_rfl ν).map (toK O K) := Iff.rfl

section Tgt

variable {O K Kc : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [CharZero K] [Field Kc] [Algebra K Kc]
  {B τ : Type} [Fintype B] [DecidableEq B] {n : ℕ} (em : B → Fin n × Fin n → τ)
  (hem : Function.Injective fun x : B × (Fin n × Fin n) => em x.1 x.2)
  (ν : B → Fin n → ℕ) (hν : ∀ b, Antitone (ν b))
  (h hi : B → Matrix (Fin n) (Fin n) K) (hh : ∀ b, hi b * h b = 1)
  (M : AddSubgroup Kc)
  (ι : B → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]
  (e e' : ∀ b, ι b → MvPolynomial (Fin n × Fin n) K)

def Ei (i : ∀ b, ι b) : MvPolynomial τ K := ∏ b, rename (em b) (rowAct K (hi b) (e b (i b)))

def Ei' (i : ∀ b, ι b) : MvPolynomial τ K := ∏ b, rename (em b) (rowAct K (h b).transpose (e' b (i b)))

include hh in
theorem tgt1 (hsp : ∀ b, dualWeyl K n n (ν b) ≤ Submodule.span K (Set.range (e b)))
    (F : B → MvPolynomial (Fin n × Fin n) K) (hF : ∀ b, F b ∈ dualWeyl K n n (ν b)) :
    ∏ b, rename (em b) (F b) ∈ Submodule.span K (Set.range (Ei em hi ι e)) := by
  have hh' : ∀ b, h b * hi b = 1 := fun b => mul_eq_one_comm.1 (hh b)
  refine prod_span (R := K) (fun b => Set.range fun i : ι b => rename (em b) (rowAct K (hi b) (e b i))) _ ?_ _ ?_
  · intro f hf
    choose i hi' using hf
    refine Submodule.subset_span ⟨i, ?_⟩
    exact Finset.prod_congr rfl fun b _ => hi' b
  · intro b
    have h2 : rowAct K (h b) (F b) ∈ Submodule.span K (Set.range (e b)) :=
      hsp b (dualWeylRowStable K n n (ν b) (h b) (F b) (hF b))
    have h3 : F b = rowAct K (hi b) (rowAct K (h b) (F b)) := by rw [rowAct_rowAct, hh' b, rowAct_one]
    rw [h3]
    have h4 := Submodule.mem_map_of_mem (f := ((rename (em b) : MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial τ K).comp
      (rowAct K (hi b))).toLinearMap) h2
    rw [Submodule.map_span, ← Set.range_comp] at h4
    exact h4

theorem tgt2 {ι' : Type} (E : ι' → MvPolynomial τ K) (t : MvPolynomial τ K) (ht : t ∈ Submodule.span K (Set.range E)) :
    map (algebraMap K Kc) t ∈ Submodule.span Kc (Set.range fun i => map (algebraMap K Kc) (E i)) := by
  induction ht using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

include hem hh in
theorem tgt3 (hFP : FockProd)
    (hee : ∀ b i k, fockR (e b i) (e' b k) = if i = k then fockR (hw K le_rfl (ν b)) (hw K le_rfl (ν b)) else 0)
    (i k : ∀ b, ι b) : fockR (Ei em hi ι e i) (Ei' em h ι e' k) = if i = k then ∏ b, cN K (ν b) else 0 := by
  unfold Ei Ei'
  rw [hFP K B (Fin n × Fin n) τ em hem]
  have h4 : ∀ b, fockR (rowAct K (hi b) (e b (i b))) (rowAct K (h b).transpose (e' b (k b))) =
      if i b = k b then cN K (ν b) else 0 := by
    intro b
    rw [Top.fockRRowAct, rowAct_rowAct, ← Matrix.transpose_mul, hh b, Matrix.transpose_one, rowAct_one]
    exact hee b (i b) (k b)
  rw [Finset.prod_congr rfl fun b _ => h4 b]
  by_cases hik : i = k
  · subst hik; simp
  · rw [if_neg hik]
    obtain ⟨b, hb⟩ := Function.ne_iff.1 hik
    exact Finset.prod_eq_zero (Finset.mem_univ b) (if_neg hb)

include hem hh in
theorem tgt5 (hFP : FockProd)
    (hee : ∀ b i k, fockR (e b i) (e' b k) = if i = k then fockR (hw K le_rfl (ν b)) (hw K le_rfl (ν b)) else 0)
    (a : (∀ b, ι b) → Kc) (k : ∀ b, ι b) :
    fockR (∑ i, a i • map (algebraMap K Kc) (Ei em hi ι e i)) (map (algebraMap K Kc) (Ei' em h ι e' k)) =
      a k * ∏ b, cN Kc (ν b) := by
  rw [fockR_sum_left, Finset.sum_eq_single k]
  · rw [fockR_smul_left, Top.fockRMap, tgt3 em hem ν h hi hh ι e e' hFP hee, if_pos rfl, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun b _ => map_cN K Kc _ _
  · intro i _ hik
    rw [fockR_smul_left, Top.fockRMap, tgt3 em hem ν h hi hh ι e e' hFP hee, if_neg hik, map_zero, mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk


include hem hh in
theorem tgt_core (hFP : FockProd)
    (he : ∀ b i, e b i ∈ (weyl O n n le_rfl (ν b)).map (toK O K)) (he' : ∀ b i, e' b i ∈ (dualWeyl O n n (ν b)).map (toK O K))
    (hee : ∀ b i k, fockR (e b i) (e' b k) = if i = k then fockR (hw K le_rfl (ν b)) (hw K le_rfl (ν b)) else 0)
    (hsp : ∀ b, dualWeyl K n n (ν b) ≤ Submodule.span K (Set.range (e b))) (y : MvPolynomial τ Kc)
    (hy : y ∈ Submodule.span Kc {z | ∃ F : B → MvPolynomial (Fin n × Fin n) K, (∀ b, F b ∈ dualWeyl K n n (ν b)) ∧
      z = map (algebraMap K Kc) (∏ b, rename (em b) (F b))})
    (hp : ∀ Q : B → MvPolynomial (Fin n × Fin n) K, (∀ b, Q b ∈ (dualWeyl O n n (ν b)).map (toK O K)) →
      ∃ a ∈ M, fockR y (map (algebraMap K Kc) (∏ b, rename (em b) (rowAct K (h b).transpose (Q b)))) =
        a * ∏ b, cN Kc (ν b)) :
    y ∈ AddSubgroup.closure {z | ∃ a ∈ M, ∃ F : B → MvPolynomial (Fin n × Fin n) K,
      (∀ b, F b ∈ deltaL O K n (ν b) (h b)) ∧ z = a • map (algebraMap K Kc) (∏ b, rename (em b) (F b))} := by
  have : CharZero Kc := charZero_of_injective_algebraMap (algebraMap K Kc).injective
  have h2 : y ∈ Submodule.span Kc (Set.range fun i => map (algebraMap K Kc) (Ei em hi ι e i)) := by
    refine (Submodule.span_le.2 ?_) hy
    rintro _ ⟨F, hF, rfl⟩
    exact tgt2 _ _ (tgt1 em ν h hi hh ι e hsp F hF)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Kc).1 h2
  have hc : (∏ b, cN Kc (ν b)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => cN_ne Kc (ν b)
  have h6 : ∀ k, a k ∈ M := by
    intro k
    obtain ⟨a', ha', h7⟩ := hp (fun b => e' b (k b)) fun b => he' b (k b)
    have h5 := tgt5 (Kc := Kc) em hem ν h hi hh ι e e' hFP hee a k
    rw [ha] at h5
    have : a k = a' := mul_right_cancel₀ hc (h5.symm.trans h7)
    rw [this]; exact ha'
  rw [← ha]
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
  refine ⟨a i, h6 i, fun b => rowAct K (hi b) (e b (i b)), fun b => ?_, ?_⟩
  · rw [mem_deltaL', rowAct_rowAct, hh b, rowAct_one]
    exact he b (i b)
  · unfold Ei
    rfl

end Tgt

section Tgt'

variable {O K Kc : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [CharZero K] [Field Kc] [Algebra K Kc]
  {B τ : Type} [Fintype B] [DecidableEq B] {n : ℕ} (em : B → Fin n × Fin n → τ)
  (hem : Function.Injective fun x : B × (Fin n × Fin n) => em x.1 x.2)
  (ν : B → Fin n → ℕ) (hν : ∀ b, Antitone (ν b))
  (h hi : B → Matrix (Fin n) (Fin n) K) (hh : ∀ b, hi b * h b = 1)
  (M : AddSubgroup Kc)

include hem hν hh in
theorem tgt_abs (hDB : DualBases) (hFP : FockProd) (y : MvPolynomial τ Kc)
    (hy : y ∈ Submodule.span Kc {z | ∃ F : B → MvPolynomial (Fin n × Fin n) K, (∀ b, F b ∈ dualWeyl K n n (ν b)) ∧
      z = map (algebraMap K Kc) (∏ b, rename (em b) (F b))})
    (hp : ∀ Q : B → MvPolynomial (Fin n × Fin n) K, (∀ b, Q b ∈ (dualWeyl O n n (ν b)).map (toK O K)) →
      ∃ a ∈ M, fockR y (map (algebraMap K Kc) (∏ b, rename (em b) (rowAct K (h b).transpose (Q b)))) =
        a * ∏ b, cN Kc (ν b)) :
    y ∈ AddSubgroup.closure {z | ∃ a ∈ M, ∃ F : B → MvPolynomial (Fin n × Fin n) K,
      (∀ b, F b ∈ deltaL O K n (ν b) (h b)) ∧ z = a • map (algebraMap K Kc) (∏ b, rename (em b) (F b))} := by
  choose ι fι dι e e' he he' hee hsp using fun b => hDB O K n (ν b) (hν b)
  exact @tgt_core O K Kc _ _ _ _ _ _ _ _ _ B τ _ _ n em hem ν h hi hh M ι fι dι e e' hFP he he' hee hsp y hy hp

end Tgt'

end Formalism.L2.PairingIndexBounds.Ent
end
end

