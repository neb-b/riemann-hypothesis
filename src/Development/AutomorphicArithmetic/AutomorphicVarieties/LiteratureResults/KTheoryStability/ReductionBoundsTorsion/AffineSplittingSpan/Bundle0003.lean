module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Bundle0001
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreDefs
section
noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

abbrev Bi (P Q : Type) (a b : ℕ) : Type := (Fin a → Q) → (Fin b → P) → ℝ

def dh {a b : ℕ} (F : Bi P Q (a + 1) b) : Bi P Q (a + 2) b := fun x y => dc (fun x' => F x' y) x

def dv {a b : ℕ} (F : Bi P Q a (b + 1)) : Bi P Q a (b + 2) := fun x y => dc (F x) y

def PInv (pr : P →* Q) {a b : ℕ} (F : Bi P Q a b) : Prop :=
  ∀ (g : P) x y, F (fun i => pr g * x i) (fun j => g * y j) = F x y

def Ru (u : Q) {a b : ℕ} (F : Bi P Q a b) : Bi P Q a b := fun x y => F (fun i => x i * u) y

def Rt (t : P) {a b : ℕ} (F : Bi P Q a b) : Bi P Q a b := fun x y => F x (fun j => y j * t)

def Tc (t : P) {a b : ℕ} (F : Bi P Q a b) : Bi P Q a b := fun x y => F x (fun j => t⁻¹ * y j * t)

def Hv (t : P) {a b : ℕ} (F : Bi P Q a (b + 1)) : Bi P Q a b :=
  fun x y => PrismSpan.prism (fun p => p * t) (F x) y

def RuL (u : Q) (a b : ℕ) : Module.End ℝ (Bi P Q a b) where
  toFun := Ru u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def TcL (t : P) (a b : ℕ) : Module.End ℝ (Bi P Q a b) where
  toFun := Tc t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cat {a c : ℕ} (x : Fin a → Q) (z : Fin c → Q) (n : ℕ) : Fin n → Q := fun i =>
  if h : (i : ℕ) < a then x ⟨i, h⟩ else if h' : (i : ℕ) - a < c then z ⟨(i : ℕ) - a, h'⟩ else 1

def zz (pr : P →* Q) {n : ℕ} (b : (Fin n → Q) → ℝ) (a c : ℕ) : Bi P Q a c :=
  fun x y => b (cat x (fun j => pr (y j)) n)

def Wtop (pr : P →* Q) {n : ℕ} (b : (Fin n → Q) → ℝ) : Bi P Q 1 n := fun _ y => b (fun j => pr (y j))

def QC {n : ℕ} (b : (Fin (n + 1) → Q) → ℝ) : Prop :=
  (∀ (g : Q) x, b (fun i => g * x i) = b x) ∧ dc b = 0

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.ProdEmbNeOne
section
noncomputable section

open NumberField InfinitePlace Polynomial

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

def mulVHom {L : Type} [Field L] [NumberField L] (n r : ℕ) (v : 𝓞 L) :
    Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) →* Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) where
  toFun := mulV n r v
  map_one' := by simp [mulV]
  map_mul' x y := by simp [mulV, smul_add]

theorem prod_emb_ne_one {L : Type} [Field L] [NumberField L] (m : ℕ) (v : (𝓞 L)ˣ)
    (hv : ∀ a : InfinitePlace L → ℕ, 0 < ∑ w, a w → ∑ w, a w ≤ m → ∏ w, (w (v : L)) ^ a w ≠ 1)
    (q : ℕ) (hq : q + 1 ≤ m) (σs : Fin (q + 1) → (L →+* ℂ)) :
    ∏ i, σs i (algebraMap (𝓞 L) L (v : 𝓞 L)) ≠ 1 := by
  classical
  intro h
  have hn : ∏ i, (InfinitePlace.mk (σs i)) (algebraMap (𝓞 L) L (v : 𝓞 L)) = 1 := by
    have := congrArg norm h
    rw [norm_prod, norm_one] at this
    simpa [InfinitePlace.apply] using this
  let g : Fin (q + 1) → InfinitePlace L := fun i => InfinitePlace.mk (σs i)
  let a : InfinitePlace L → ℕ := fun w => (Finset.univ.filter fun i => g i = w).card
  have hsum : ∑ w, a w = q + 1 := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin (q + 1))))
      (t := (Finset.univ : Finset (InfinitePlace L))) (f := g) (fun _ _ => Finset.mem_univ _)
    simpa [a] using this.symm
  have hprod : ∏ w, (w (algebraMap (𝓞 L) L (v : 𝓞 L))) ^ a w = 1 := by
    rw [← hn, ← Finset.prod_fiberwise Finset.univ g]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => w (algebraMap (𝓞 L) L (v : 𝓞 L))), Finset.prod_const]
    intro i hi
    have hgi : g i = w := (Finset.mem_filter.mp hi).2
    simp only [g] at hgi
    rw [hgi]
  exact hv a (by omega) (by omega) hprod

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

open PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes in
theorem PositivityTheory.KB.SplitAffineSpectral.eigen : PositivityTheory.KB.SplitAffineSpectral.Eigen := by
  intro L _ _ _ m v hv n r q hq
  classical
  let lam : Fin n × Fin r × (L →+* ℂ) → ℂ := fun j => j.2.2 (algebraMap (𝓞 L) L (v : 𝓞 L))
  let β : Fin n × Fin r × (L →+* ℂ) → Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) → ℂ :=
    fun j x => j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd (Additive.toMul x) j.1 j.2.1))
  refine ⟨∏ J : Fin (q + 1) → Fin n × Fin r × (L →+* ℂ), gpoly (∏ i, lam (J i)), ?_, ?_⟩
  · rw [Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun J _ => ?_
    rw [gpoly_eval_one, Ne, Complex.normSq_eq_zero, sub_eq_zero]
    exact fun h => prod_emb_ne_one m v hv q hq (fun i => (J i).2.2) h.symm
  · intro α
    have hβ : ∀ j x, β j (Additive.ofMul (mulVHom n r (v : 𝓞 L) x)) = lam j * β j (Additive.ofMul x) := by
      intro j x
      change j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd (mulV n r (v : 𝓞 L) x) j.1 j.2.1)) =
        j.2.2 (algebraMap (𝓞 L) L (v : 𝓞 L)) * j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd x j.1 j.2.1))
      simp only [mulV, toAdd_ofAdd, Matrix.smul_apply, smul_eq_mul, map_mul]
    exact cup_kill (mulVHom n r (v : 𝓞 L)) β lam hβ (fun α => mat_span L n r α) q α
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanCup
section
noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

section General

variable {Y : Type}

theorem dc_dc : ∀ (m : ℕ) (F : (Fin (m + 1) → Y) → ℝ), dc (dc F) = 0 := by
  intro m
  induction m with
  | zero =>
    intro F
    funext y
    simp [dc, Fin.sum_univ_succ]
    have hCD : (fun j : Fin 1 => y (Fin.succAbove 1 (Fin.succAbove 1 j))) =
        fun j => y (Fin.succAbove 2 (Fin.succAbove 1 j)) := by
      funext j
      rw [Subsingleton.elim j (0 : Fin 1)]
      rfl
    linear_combination congrArg F hCD
  | succ m ih =>
    intro F
    funext y
    rw [← Fin.cons_self_tail y, dc_cons]
    have e : (fun w' => dc F (Fin.cons (y 0) w')) = F - dc (fun w' => F (Fin.cons (y 0) w')) := by
      funext w'; rw [dc_cons]; rfl
    rw [e, dc_sub, ih]
    simp

theorem dc_neg {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : dc (-F) = -dc F := by
  funext y; simp [dc, Finset.sum_neg_distrib]

theorem prism_zero (φ : Y → Y) : ∀ {n : ℕ}, prism φ (0 : (Fin (n + 1) → Y) → ℝ) = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext y
    rw [prism_succ]
    change 0 - prism φ (0 : (Fin (n + 1) → Y) → ℝ) (Fin.tail y) = 0
    simp only [ih, Pi.zero_apply, sub_zero]

end General

section Grp

variable {P : Type} [Group P]

theorem dc_inv (S : Set P) {m : ℕ} (F : (Fin (m + 1) → P) → ℝ) (hF : InvS S F) : InvS S (dc F) := by
  intro g hg y
  simp only [dc]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg _ (hF g hg _)

def tcup (l : Additive P →+ ℝ) {n : ℕ} (e : (Fin (n + 1) → P) → ℝ) : (Fin (n + 2) → P) → ℝ :=
  fun y => l (Additive.ofMul ((y 0)⁻¹ * y 1)) * e (Fin.tail y)

theorem tail_eq' {α : Type} {k : ℕ} (q : Fin (k + 1) → α) : Fin.tail q = fun i => q i.succ := rfl

theorem dc_tcup (l : Additive P →+ ℝ) {n : ℕ} (e : (Fin (n + 1) → P) → ℝ) :
    dc (tcup l e) = -tcup l (dc e) := by
  funext y
  simp [dc, tcup, Fin.sum_univ_succ, tail_eq']
  simp only [pow_succ, mul_add, Finset.mul_sum, neg_add, ← Finset.sum_neg_distrib]
  ring_nf

theorem tcup_inv (l : Additive P →+ ℝ) (S : Set P) {n : ℕ} (e : (Fin (n + 1) → P) → ℝ) (he : InvS S e) :
    InvS S (tcup l e) := by
  intro g hg y
  simp only [tcup]
  rw [show (g * y 0)⁻¹ * (g * y 1) = (y 0)⁻¹ * y 1 by group]
  congr 1
  exact he g hg (Fin.tail y)

theorem tcup_add (l : Additive P →+ ℝ) {n : ℕ} (e f : (Fin (n + 1) → P) → ℝ) :
    tcup l (e + f) = tcup l e + tcup l f := by
  funext y; simp [tcup, mul_add]

theorem tcup_sum (l : Additive P →+ ℝ) {n k : ℕ} (a : Fin k → ℝ) (F : Fin k → (Fin (n + 1) → P) → ℝ) :
    tcup l (∑ i, a i • F i) = ∑ i, a i • tcup l (F i) := by
  funext y
  simp only [tcup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem tcup_cupH (l : Additive P →+ ℝ) {q : ℕ} (β : Fin q → (Additive P →+ ℝ)) :
    tcup l (cupH β) = cupH (Fin.cons l β) := by
  funext y
  simp [tcup, cupH, Fin.prod_univ_succ, Fin.tail]

end Grp

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.TransferAlt
section
noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

open PositivityTheory.KB.SplitAffineSpectral Polynomial

theorem pow_intertwine {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (T : Module.End ℝ V) (T' : Module.End ℝ W) (L : V →ₗ[ℝ] W) (h : ∀ v, T' (L v) = L (T v)) :
    ∀ (n : ℕ) (v : V), (T' ^ n) (L v) = L ((T ^ n) v)
  | 0, v => rfl
  | n + 1, v => by
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, h, pow_intertwine T T' L h n]

theorem aeval_intertwine {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (T : Module.End ℝ V) (T' : Module.End ℝ W) (L : V →ₗ[ℝ] W) (h : ∀ v, T' (L v) = L (T v))
    (f : ℝ[X]) (v : V) : aeval T' f (L v) = L (aeval T f v) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      pow_intertwine T T' L h n, map_smul]

theorem pow_mem {V : Type} [AddCommGroup V] [Module ℝ V] (T : Module.End ℝ V) (S : Submodule ℝ V)
    (hT : ∀ v ∈ S, T v ∈ S) : ∀ (n : ℕ) (v : V), v ∈ S → (T ^ n) v ∈ S
  | 0, v, hv => hv
  | n + 1, v, hv => by
    rw [pow_succ, Module.End.mul_apply]
    exact pow_mem T S hT n _ (hT v hv)

theorem aeval_mem {V : Type} [AddCommGroup V] [Module ℝ V] (T : Module.End ℝ V) (S : Submodule ℝ V)
    (hT : ∀ v ∈ S, T v ∈ S) (f : ℝ[X]) (v : V) (hv : v ∈ S) : aeval T f v ∈ S := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply]; exact S.add_mem hp hq
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact S.smul_mem a (pow_mem T S hT n v hv)

def invSub {P : Type} [Group P] (S : Set P) (m : ℕ) : Submodule ℝ ((Fin m → P) → ℝ) where
  carrier := {F | InvS S F}
  add_mem' {F G} hF hG g hg y := by simp only [Pi.add_apply, hF g hg y, hG g hg y]
  zero_mem' g _ y := rfl
  smul_mem' r F hF g hg y := by simp only [Pi.smul_apply, hF g hg y]

def dcL (Y : Type) (m : ℕ) : ((Fin (m + 1) → Y) → ℝ) →ₗ[ℝ] ((Fin (m + 2) → Y) → ℝ) where
  toFun := dc
  map_add' F G := by
    funext y; simp only [dc, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r F := by
    funext y; simp only [dc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

def pullL {X Y : Type} (g : X → Y) (m : ℕ) : ((Fin m → Y) → ℝ) →ₗ[ℝ] ((Fin m → X) → ℝ) where
  toFun F x := F fun i => g (x i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

namespace PositivityTheory.KB.SplitAffineSpectral

open PrismTransfer Polynomial

theorem transfer : Transfer := by
  intro P Q A _ _ _ pr s hs u hu ι hι hran φ hφ m hA q hq
  obtain ⟨f, hf1, hfA⟩ := hA q hq
  refine ⟨f, hf1, fun c hc hcc => ?_⟩
  set t := s u with ht
  have hker : ∀ k : P, k ∈ (pr.ker : Set P) ↔ pr k = 1 := fun k => MonoidHom.mem_ker

  let ρ : P → P := fun y => y * (s (pr y))⁻¹
  have hρk : ∀ y, ∃ a, ι a = ρ y := fun y => (hran _).1 (by simp [ρ, hs])
  let ρA : P → A := fun y => Classical.choose (hρk y)
  have hρA : ∀ y, ι (ρA y) = ρ y := fun y => Classical.choose_spec (hρk y)
  have hιk : ∀ b, pr (ι b) = 1 := fun b => (hran _).2 ⟨b, rfl⟩
  have hρmul : ∀ k y, pr k = 1 → ρ (k * y) = k * ρ y := by
    intro k y hk; simp only [ρ, map_mul, hk, one_mul, mul_assoc]
  have hρAmul : ∀ b y, ρA (ι b * y) = b * ρA y := by
    intro b y; apply hι; rw [map_mul, hρA, hρA, hρmul _ _ (hιk b)]
  have hcomm : ∀ g : Q, s g * t = t * s g := by
    intro g; rw [ht, ← map_mul, ← map_mul, hu]
  have hρconj : ∀ y, ρ (t⁻¹ * y * t) = t⁻¹ * ρ y * t := by
    intro y
    have hp : pr (t⁻¹ * y * t) = pr y := by
      rw [map_mul, map_mul, map_inv, ht, hs, hu, mul_inv_cancel_left]
    have hc' : (s (pr y))⁻¹ * t = t * (s (pr y))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    show t⁻¹ * y * t * (s (pr (t⁻¹ * y * t)))⁻¹ = t⁻¹ * (y * (s (pr y))⁻¹) * t
    rw [hp]
    simp only [mul_assoc, hc']
  have hρAconj : ∀ y, ρA (t⁻¹ * y * t) = φ (ρA y) := by
    intro y; apply hι; rw [hρA, hρconj, hφ, hρA]

  let cA : (Fin (q + 2) → A) → ℝ := fun x => c fun i => ι (x i)
  have hcA : InvS Set.univ cA := by
    intro b _ x
    simp only [cA, map_mul]
    exact hc (ι b) ((hker _).2 (hιk b)) _
  have hccA : dc cA = 0 := by
    funext x
    have := congrFun hcc (fun i => ι (x i))
    simpa [dc, cA] using this
  obtain ⟨eA, heA, hfe⟩ := hfA cA hcA hccA

  let T : (n : ℕ) → Module.End ℝ ((Fin n → P) → ℝ) := fun n => mapOp (fun y => t⁻¹ * y * t) n
  have hTR : ∀ (n : ℕ) (g : (Fin n → A) → ℝ),
      T n (pullL ρA n g) = pullL ρA n (mapOp φ n g) := by
    intro n g; funext y; simp only [T, mapOp, pullL, LinearMap.coe_mk, AddHom.coe_mk, hρAconj]
  have hTd : ∀ (n : ℕ) (F : (Fin (n + 1) → P) → ℝ), T (n + 2) (dcL P n F) = dcL P n (T (n + 1) F) :=
    fun n F => rfl
  have hRd : ∀ (n : ℕ) (g : (Fin (n + 1) → A) → ℝ), pullL ρA (n + 2) (dcL A n g) = dcL P n (pullL ρA (n + 1) g) :=
    fun n g => rfl

  have hpr : c = pullL ρA (q + 2) cA - dc (prism ρ q c) := by
    funext y
    have h1 := prism_htpy ρ q c y
    rw [hcc] at h1
    have h0 : prism ρ (q + 1) (fun _ => (0 : ℝ)) y = 0 := prism_zero ρ (q + 1) y
    have h2 : pullL ρA (q + 2) cA y = c (ρ ∘ y) := by
      simp only [pullL, cA, LinearMap.coe_mk, AddHom.coe_mk, hρA]; rfl
    simp only [Pi.sub_apply, h2]
    have h3 : (0 : (Fin (q + 3) → P) → ℝ) = fun _ => 0 := rfl
    rw [h3, h0] at h1
    linarith

  have hprismInv : InvS (pr.ker : Set P) (prism ρ q c) := by
    intro k hk y
    rw [prism_smul ρ k (fun y => hρmul k y ((hker k).1 hk)) q c y]
    congr 1
    funext z
    exact hc k hk z
  have hTinv : ∀ (n : ℕ), ∀ F ∈ invSub (pr.ker : Set P) n, T n F ∈ invSub (pr.ker : Set P) n := by
    intro n F hF k hk y
    simp only [T, mapOp, LinearMap.coe_mk, AddHom.coe_mk]
    have hk' : t⁻¹ * k * t ∈ (pr.ker : Set P) := by
      rw [hker] at hk ⊢
      rw [map_mul, map_mul, hk, mul_one, map_inv, inv_mul_cancel]
    have := hF _ hk' (fun i => t⁻¹ * y i * t)
    simp only [mul_assoc, mul_inv_cancel_left] at this ⊢
    exact this
  refine ⟨pullL ρA (q + 1) eA - aeval (T (q + 1)) f (prism ρ q c), ?_, ?_⟩
  · intro k hk y
    obtain ⟨b, rfl⟩ := (hran k).1 ((hker k).1 hk)
    have h1 : aeval (T (q + 1)) f (prism ρ q c) ∈ invSub (pr.ker : Set P) (q + 1) :=
      aeval_mem _ _ (hTinv (q + 1)) f _ hprismInv
    simp only [Pi.sub_apply]
    rw [h1 (ι b) hk y]
    congr 1
    simp only [pullL, LinearMap.coe_mk, AddHom.coe_mk, hρAmul]
    exact heA b trivial _
  · have e1 : aeval (T (q + 2)) f c =
        aeval (T (q + 2)) f (pullL ρA (q + 2) cA) - aeval (T (q + 2)) f (dcL P q (prism ρ q c)) := by
      conv_lhs => rw [hpr]
      rw [map_sub]
      rfl
    change aeval (T (q + 2)) f c = _
    rw [e1, aeval_intertwine (mapOp φ (q + 2)) (T (q + 2)) (pullL ρA (q + 2)) (hTR (q + 2)),
      aeval_intertwine (T (q + 1)) (T (q + 2)) (dcL P q) (hTd q), hfe]
    rw [show dc eA = dcL A q eA from rfl, hRd]
    rw [← map_sub]
    rfl

end PositivityTheory.KB.SplitAffineSpectral

end
end

