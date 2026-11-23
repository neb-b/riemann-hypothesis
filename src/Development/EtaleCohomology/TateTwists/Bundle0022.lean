module

public import Development.EtaleCohomology.TateTwists.Bundle0009
public import Development.EtaleCohomology.TateTwists.Bundle0007
public import Development.EtaleCohomology.TateTwists.Bundle0001
public import Development.EtaleCohomology.TateTwists.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0013
public import Development.EtaleCohomology.TateTwists.Bundle0004
public import Development.EtaleCohomology.TateTwists.Bundle0002

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.LeafAwPf
section
open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AwPf

abbrev sb {n : ℕ} (j l : ℕ) (h : j + l ≤ n) : SimplexCategory.mk l ⟶ SimplexCategory.mk n :=
  SimplexCategory.subinterval j l h

@[simp] lemma sb_apply {n : ℕ} (j l : ℕ) (h : j + l ≤ n) (i : Fin (l + 1)) :
    (((sb j l h).toOrderHom i : Fin (n + 1)) : ℕ) = i + j := rfl

lemma m_last (p r : ℕ) (h1 : 0 + (p + 1) ≤ p + r + 1) (h2 : 0 + p ≤ p + r + 1) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫ sb 0 (p + 1) h1 = sb 0 p h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma m_zero (p r : ℕ) (h1 : p + (r + 1) ≤ p + r + 1) (h2 : (p + 1) + r ≤ p + r + 1) :
    SimplexCategory.δ 0 ≫ sb p (r + 1) h1 = sb (p + 1) r h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma m_lo (p r : ℕ) (k : Fin (p + r + 2)) (hk : (k : ℕ) ≤ p) (h1 : 0 + p ≤ p + r)
    (h2 : 0 + (p + 1) ≤ p + r + 1) :
    sb 0 p h1 ≫ SimplexCategory.δ k = SimplexCategory.δ (⟨k, by omega⟩ : Fin (p + 2)) ≫ sb 0 (p + 1) h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma simplex_subinterval_back_comp_face_within_front (p r : ℕ) (k : Fin (p + r + 2)) (hk : (k : ℕ) ≤ p) (h1 : p + r ≤ p + r)
    (h2 : (p + 1) + r ≤ p + r + 1) :
    sb p r h1 ≫ SimplexCategory.δ k = sb (p + 1) r h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma m_hi (p r : ℕ) (k : Fin (p + r + 2)) (hk : p < (k : ℕ)) (h1 : 0 + p ≤ p + r)
    (h2 : 0 + p ≤ p + r + 1) :
    sb 0 p h1 ≫ SimplexCategory.δ k = sb 0 p h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma simplex_subinterval_back_comp_face_above_front (p r : ℕ) (k : Fin (p + r + 2)) (hk : p < (k : ℕ)) (h1 : p + r ≤ p + r)
    (h2 : p + (r + 1) ≤ p + r + 1) :
    sb p r h1 ≫ SimplexCategory.δ k = SimplexCategory.δ (⟨k - p, by omega⟩ : Fin (r + 2)) ≫ sb p (r + 1) h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

def T (n p r : ℕ) (h : p + r ≤ n) : Pr n := ⟨p, r, sb 0 p (by omega), sb p r h⟩

noncomputable def S (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then Finsupp.single (T n x.1 x.2 h) 1 else 0

noncomputable def g1 (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then Pr.d₁ (T n x.1 x.2 h) else 0

noncomputable def g2 (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then (-1 : ℤ) ^ x.1 • Pr.d₂ (T n x.1 x.2 h) else 0

lemma aw_eq (n : ℕ) : Pr.aw n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, S n x := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range (fun k => S n (k, n - k))]
  unfold Pr.aw
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.isLt
  simp only [S]
  rw [dite_eq_left (by omega)]
  rfl

lemma bd_sum {N : ℕ} {ι : Type*} (s : Finset ι) (g : ι → Pr N →₀ ℤ) :
    Pr.bd (∑ x ∈ s, g x) = ∑ x ∈ s, Pr.bd (g x) := by
  unfold Pr.bd
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.smul_sum]
  exact Finset.sum_comm

lemma d_S (n : ℕ) (x : ℕ × ℕ) : Pr.d n (S n x) = g1 n x + g2 n x := by
  unfold S g1 g2
  split_ifs with h
  · simp only [Pr.d, Finsupp.linearCombination_single, one_smul]
    rfl
  · simp

lemma split_sum {M : Type*} [AddCommMonoid M] (p r : ℕ) (f : Fin (p + r + 2) → M) :
    ∑ k, f k = ∑ i : Fin (p + 1), f ⟨i, by omega⟩ + ∑ j : Fin (r + 1), f ⟨p + 1 + j, by omega⟩ := by
  rw [← (finCongr (by omega : (p + 1) + (r + 1) = p + r + 2)).sum_comp, Fin.sum_univ_add]
  rfl

lemma bd_single (n : ℕ) (z : Pr n) : Pr.bd (Finsupp.single z 1) =
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • Finsupp.single
      (⟨z.1, z.2.1, z.2.2.1 ≫ SimplexCategory.δ k, z.2.2.2 ≫ SimplexCategory.δ k⟩ : Pr (n + 1)) 1 := by
  unfold Pr.bd
  simp [Pr.push]

lemma key (p r : ℕ) :
    Pr.d₁ (T (p + r + 1) (p + 1) r (by omega)) + (-1 : ℤ) ^ p • Pr.d₂ (T (p + r + 1) p (r + 1) (by omega)) =
      Pr.bd (Finsupp.single (T (p + r) p r le_rfl) 1) := by
  have e1 : Pr.d₁ (T (p + r + 1) (p + 1) r (by omega)) = ∑ i : Fin (p + 2),
      Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ sb 0 (p + 1) (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ (i : ℕ)) := rfl
  have e2 : Pr.d₂ (T (p + r + 1) p (r + 1) (by omega)) = ∑ j : Fin (r + 2),
      Finsupp.single (⟨p, r, sb 0 p (by omega), SimplexCategory.δ j ≫ sb p (r + 1) (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ (j : ℕ)) := rfl
  rw [e1, e2, bd_single, split_sum, Fin.sum_univ_castSucc (n := p + 1), Fin.sum_univ_succ (n := r + 1)]
  have hlo : ∀ i : Fin (p + 1),
      (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (⟨(T (p + r) p r le_rfl).1, (T (p + r) p r le_rfl).2.1,
        (T (p + r) p r le_rfl).2.2.1 ≫ SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + r + 2)),
        (T (p + r) p r le_rfl).2.2.2 ≫ SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + r + 2))⟩ : Pr (p + r + 1)) 1 =
      Finsupp.single (⟨p, r, SimplexCategory.δ i.castSucc ≫ sb 0 (p + 1) (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.castSucc i : Fin (p + 2)) : ℕ)) := by
    intro i
    have hi := i.isLt
    simp only [T]
    rw [m_lo p r _ (by show (i : ℕ) ≤ p; omega) _ (by omega), simplex_subinterval_back_comp_face_within_front p r _ (by show (i : ℕ) ≤ p; omega) _ (by omega),
      Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl
  have hhi : ∀ j : Fin (r + 1),
      (-1 : ℤ) ^ (p + 1 + (j : ℕ)) • Finsupp.single (⟨(T (p + r) p r le_rfl).1, (T (p + r) p r le_rfl).2.1,
        (T (p + r) p r le_rfl).2.2.1 ≫ SimplexCategory.δ (⟨p + 1 + j, by omega⟩ : Fin (p + r + 2)),
        (T (p + r) p r le_rfl).2.2.2 ≫ SimplexCategory.δ (⟨p + 1 + j, by omega⟩ : Fin (p + r + 2))⟩ : Pr (p + r + 1)) 1 =
      (-1 : ℤ) ^ p • Finsupp.single (⟨p, r, sb 0 p (by omega), SimplexCategory.δ j.succ ≫ sb p (r + 1) (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.succ j : Fin (r + 2)) : ℕ)) := by
    intro j
    have hj := j.isLt
    simp only [T]
    rw [m_hi p r _ (by show p < p + 1 + (j : ℕ); omega) _ (by omega), simplex_subinterval_back_comp_face_above_front p r _ (by show p < p + 1 + (j : ℕ); omega) _ (by omega),
      Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one]
    have hf : (⟨p + 1 + (j : ℕ) - p, by omega⟩ : Fin (r + 2)) = j.succ := by
      ext; simp; omega
    rw [hf, Fin.val_succ]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun i _ => hlo i), Finset.sum_congr rfl (fun j _ => hhi j), ← Finset.smul_sum,
    m_last p r (by omega) (by omega), m_zero p r (by omega) (by omega), smul_add]
  have hc : Finsupp.single (⟨p, r, sb 0 p (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.last (p + 1) : Fin (p + 2)) : ℕ)) +
      (-1 : ℤ) ^ p • Finsupp.single (⟨p, r, sb 0 p (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((0 : Fin (r + 2)) : ℕ)) = 0 := by
    rw [Finsupp.smul_single, ← Finsupp.single_add]
    simp [pow_succ]
  apply eq_of_sub_eq_zero
  rw [← hc]
  abel

theorem leaf_aw_of : LateralTheory.EtaleFoundations.SteenPf.leaf_aw := by
  intro N
  set_option synthInstance.maxHeartbeats 100000 in
    rw [aw_eq, aw_eq, map_sum, bd_sum]
  simp only [d_S]
  rw [Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
  have z1 : g1 (N + 1) (0, N + 1) = 0 := by
    unfold g1; rw [dite_eq_left (by simp)]; rfl
  have z2 : g2 (N + 1) (N + 1, 0) = 0 := by
    unfold g2; rw [dite_eq_left (by simp)]
    show (-1 : ℤ) ^ (N + 1) • (0 : Pr (N + 1) →₀ ℤ) = 0
    exact smul_zero _
  rw [z1, z2, zero_add, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨p, r⟩ := x
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  simp only at hx
  subst hx
  unfold g1 g2 S
  rw [dite_eq_left (by simp; omega), dite_eq_left (by simp; omega), dite_eq_left (by simp)]
  exact key p r

end LateralTheory.EtaleFoundations.AwPf
end

-- bundled from Development.EtaleCohomology.TateTwists.PpEvMkPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvMkPf

variable {R : Type} [CommRing R] {E : Spc} {I : Cx R}

theorem sq {X Y : Type 1} (h : X ⟶ Y) {M N : ModuleCat.{1} (ULift.{1} R)} (a : Y ⟶ M) (b : X ⟶ N) (φ : N ⟶ M)
    (H : ∀ x, a (h x) = φ (b x)) :
    (ModuleCat.free (ULift.{1} R)).map h ≫ ModuleCat.freeDesc a = ModuleCat.freeDesc b ≫ φ := by
  apply ModuleCat.free_hom_ext
  intro x
  simp [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, H]

noncomputable def eta (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    (freeP R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (I.X s).obj where
  app U := ModuleCat.freeDesc (X := ULift.{1} (Sx E k U.unop)) (↾fun x => F U.unop (ULift.down x))
  naturality U V g := sq _ _ _ _ (fun x => (hF V.unop U.unop g.unop x.down).symm)

noncomputable def phi (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ I.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) (I.X s)).symm (eta k s F hF)

theorem phi_unit (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    toSheafify Scheme.etaleTopology.{0} ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) ≫ (phi k s F hF).hom =
      eta k s F hF := by
  have := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) (I.X s)).apply_symm_apply (eta k s F hF)
  rw [Adjunction.homEquiv_unit] at this
  exact this

theorem phi_freeGen (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g))
    (U : Scheme.{0}) (x : Sx E k U) :
    ((phi k s F hF).hom.app (op U)).hom (freeGen R _ U x) = F U x := by
  have h2 := congrArg (fun f => (f.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) (phi_unit k s F hF)
  exact h2.trans (ModuleCat.freeDesc_apply _ _)

variable {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
  (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))

noncomputable def comp (p q : ℤ) (hpq : p + n = q) : ((chains R).obj E).X p ⟶ I.X q :=
  if hp : p ≤ 0 then
    (HomologicalComplex.XIsoOfEq _ (by omega : p = -((p.natAbs : ℕ) : ℤ))).hom ≫ (chainsXIso R E p.natAbs).hom ≫
      phi p.natAbs q (fun U x => a p.natAbs q (by omega) U x) (fun V U g x => ha _ _ _ V U g x)
  else 0

theorem aux {s : ℤ} (j k : ℕ) (e : j = k) (hjk : -(k : ℤ) = -(j : ℤ)) (hj : -(j : ℤ) + n = s) (hk : -(k : ℤ) + n = s) :
    (HomologicalComplex.XIsoOfEq ((chains R).obj E) hjk).hom ≫ (chainsXIso R E j).hom ≫
      phi j s (fun U x => a j s hj U x) (fun V U g x => ha _ _ _ V U g x) =
    (chainsXIso R E k).hom ≫ phi k s (fun U x => a k s hk U x) (fun V U g x => ha _ _ _ V U g x) := by
  subst e
  simp

theorem comp_neg (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) :
    comp a ha (-(k : ℤ)) s h = (chainsXIso R E k).hom ≫ phi k s (fun U x => a k s h U x) (fun V U g x => ha _ _ _ V U g x) := by
  unfold comp
  rw [dite_eq_left (by omega)]
  exact aux a ha _ _ (by omega) _ _ _

end LateralTheory.EtaleFoundations.EvMkPf

open LateralTheory.EtaleFoundations.EvMkPf in
theorem LateralTheory.EtaleFoundations.pp_ev_mk_of : LateralTheory.EtaleFoundations.pp_ev_mk := by
  intro R _ E I n a ha
  refine ⟨Cochain.mk (comp a ha), fun p s h U x => ?_⟩
  unfold ev
  rw [Cochain.mk_v, comp_neg a ha p s h, Iso.inv_hom_id_assoc]
  exact phi_freeGen _ _ _ _ U x
end

-- bundled from Development.EtaleCohomology.TateTwists.SteenrodPrismChainDifferentialSquaredEqZeroOfEta
section
open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

lemma push_d₁ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) :
    Pr.push θ z.d₁ = Pr.d₁ (N := M) ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ := by
  obtain ⟨p, r, a, b⟩ := z
  cases p with
  | zero => simp [Pr.d₁]
  | succ p =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Pr.d₁, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Category.assoc]

lemma push_d₂ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) :
    Pr.push θ z.d₂ = Pr.d₂ (N := M) ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ := by
  obtain ⟨p, r, a, b⟩ := z
  cases r with
  | zero => simp [Pr.d₂]
  | succ r =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Pr.d₂, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Category.assoc]

lemma push_single {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) (n : ℤ) :
    Pr.push θ (Finsupp.single z n) = Finsupp.single ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ n := by
  simp [Pr.push]

lemma d_push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (c : Pr N →₀ ℤ) :
    Pr.d M (Pr.push θ c) = Pr.push θ (Pr.d N c) := by
  have : (Pr.d M).comp (Pr.push θ) = (Pr.push θ).comp (Pr.d N) := by
    refine Finsupp.lhom_ext fun z n => ?_
    simp only [LinearMap.comp_apply, push_single, Pr.d, Finsupp.linearCombination_single, map_smul,
      map_add, push_d₁, push_d₂]
  exact LinearMap.congr_fun this c

theorem steenrod_prism_chain_differential_squared_eq_zero_of_etale : leaf_dbd := by
  intro N c
  unfold Pr.bd
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, d_push]

end LateralTheory.EtaleFoundations.SteenPf
end

-- bundled from Development.EtaleCohomology.TateTwists.TAwAssoc0Of
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma aw_diag {M : Type*} [AddCommMonoid M] (N : ℕ) (Φ : ℕ → ℕ → M) :
    ∑ q ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (q + 1), Φ p (q - p) =
      ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), Φ p r := by
  rw [Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_range] at hp
  rw [show N + 1 - p = N - p + 1 by omega]

lemma bil_zsmul_left {S A B C : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup C] [Module S C] (f : A →ₗ[S] B →ₗ[S] C) (c : ℤ) (a : A) (b : B) :
    f (c • a) b = c • f a b := by
  have := map_zsmul (f.flip b) c a
  simpa using this

lemma bil_sum_left {S A B C ι : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup C] [Module S C] (f : A →ₗ[S] B →ₗ[S] C) (s : Finset ι) (a : ι → A) (b : B) :
    f (∑ i ∈ s, a i) b = ∑ i ∈ s, f (a i) b := by
  have := map_sum (f.flip b) a s
  simpa using this

variable {R : Type} [CommRing R]

lemma mul_ev_right {A B C : Cx R} (P : Pair A B C) {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) {s k w : ℤ}
    (a : Sec (A.X s) U) (γ : Cochain ((chains R).obj E) B k) (t t' j j' : ℕ) (ht : t = t') (hj : j = j')
    (h : s + (-(t : ℤ) + k) = w) (h' : s + (-(t' : ℤ) + k) = w) (hl : j + t ≤ N) (hl' : j' + t' ≤ N) :
    P.mul U s (-(t : ℤ) + k) w h a (ev γ t _ rfl U (x.sub j t hl)) =
      P.mul U s (-(t' : ℤ) + k) w h' a (ev γ t' _ rfl U (x.sub j' t' hl')) := by
  subst ht hj; rfl

theorem t_aw_assoc0_of (hev : EtaleCochainEvaluationLinear) (hsub : EtaleSimplexSubfaceComposition) : t_aw_assoc0 := by
  intro R _ I J K M M' L μ ν μ' ν' hass E n m k nm mk w h1 h2 h3 h4 α β γ ab bc x y hab hx hbc hy
  refine (hev R).2.2.1 x y fun N s hs U z => ?_
  rw [hx N s hs U z, hy N s hs U z]
  let Φ : ℕ → ℕ → Sec (L.X s) U := fun p r => if h : p + r ≤ N then
    (((m * (p : ℤ) + k * ((p : ℤ) + r)).negOnePow : ℤˣ) : ℤ) •
      ν'.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + mk) s (by omega) (ev α p _ rfl U (z.sub 0 p (by omega)))
        (μ'.mul U (-(r : ℤ) + m) (-((N - p - r : ℕ) : ℤ) + k) (-((N - p : ℕ) : ℤ) + mk) (by omega)
          (ev β r _ rfl U (z.sub p r (by omega))) (ev γ (N - p - r) _ rfl U (z.sub (p + r) (N - p - r) (by omega))))
    else 0
  have hsg : ∀ a b c : ℤ, a + b = c → ((a.negOnePow : ℤˣ) : ℤ) * ((b.negOnePow : ℤˣ) : ℤ) = ((c.negOnePow : ℤˣ) : ℤ) := by
    intro a b c h; rw [← Units.val_mul, ← Int.negOnePow_add, h]
  calc _ = ∑ q : Fin (N + 1), ∑ p : Fin ((q : ℕ) + 1), Φ p ((q : ℕ) - p) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hab, bil_sum_left, Finset.smul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          have hp := p.is_lt
          have hq := q.is_lt
          simp only [Φ]
          rw [dite_eq_left (by omega), Units.smul_def, Units.smul_def, bil_zsmul_left, smul_smul,
            hsg _ _ (m * ((p : ℕ) : ℤ) + k * (((p : ℕ) : ℤ) + (((q : ℕ) - (p : ℕ) : ℕ) : ℤ)))
              (by push_cast [Nat.cast_sub (show (p : ℕ) ≤ q by omega)]; ring)]
          congr 1
          rw [hass U _ _ _ _ (-((N - p : ℕ) : ℤ) + mk) s _ _ (by omega) (by omega)]
          rw [(hsub z).1 0 q 0 p, (hsub z).1 0 q p (q - p)]
          simp only [Nat.zero_add]
          congr 1
          exact mul_ev_right _ z _ γ (N - q) (N - p - (q - p)) q (p + (q - p)) (by omega) (by omega) _ _ _ _
    _ = ∑ q ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (q + 1), Φ p (q - p) := by
          rw [← Fin.sum_univ_eq_sum_range (fun q => ∑ p ∈ Finset.range (q + 1), Φ p (q - p))]
          exact Finset.sum_congr rfl fun q _ => Fin.sum_univ_eq_sum_range (fun p => Φ p (q - p)) _
    _ = ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), Φ p r := aw_diag N Φ
    _ = ∑ p : Fin (N + 1), ∑ r : Fin (N - (p : ℕ) + 1), Φ p r := by
          rw [← Fin.sum_univ_eq_sum_range (fun p => ∑ r ∈ Finset.range (N - p + 1), Φ p r)]
          exact Finset.sum_congr rfl fun p _ => (Fin.sum_univ_eq_sum_range (fun r => Φ p r) _).symm
    _ = _ := by
          refine Finset.sum_congr rfl fun p _ => ?_
          set_option synthInstance.maxHeartbeats 100000 in
            rw [hbc, map_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hp := p.is_lt
          have hr := r.is_lt
          simp only [Φ]
          rw [dite_eq_left (by omega), Units.smul_def, Units.smul_def, map_zsmul, smul_smul,
            hsg _ _ (m * ((p : ℕ) : ℤ) + k * (((p : ℕ) : ℤ) + ((r : ℕ) : ℤ))) (by subst h3; ring)]
          rw [(hsub z).1 p (N - p) 0 r, (hsub z).1 p (N - p) r (N - p - r)]
          simp only [Nat.add_zero]

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TPairAssocPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def t_pa_tens_ex : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (T : Cx R) (τ : Pair I J T), τ.IsTensor

def t_pa_tens_univ : Prop :=
  ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor →
    ∀ μ : Pair I J K, ∃ u : T ⟶ K, τ.Compat μ (𝟙 I) (𝟙 J) u

def t_pa_precomp : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J K : Cx R} (u : I ⟶ I') (μ : Pair I' J K),
    ∃ ρ : Pair I J K, ρ.Compat μ u (𝟙 J) (𝟙 K)

def t_pa_cpush_id : Prop :=
  ∀ (R : Type) [CommRing R] (E : Spc) (I : Cx R) (n : ℤ) (x : CohomologyClass ((chains R).obj E) I n),
    cpush _ (𝟙 I) n x = x

def t_pa_cpush_htpy : Prop :=
  ∀ (R : Type) [CommRing R] (E : Spc) {I J : Cx R} (u u' : I ⟶ J), Homotopy u u' →
    ∀ (n : ℤ) (x : CohomologyClass ((chains R).obj E) I n), cpush _ u n x = cpush _ u' n x

theorem pa_sec_map_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (𝟙 F) x = x := rfl

theorem t_pair_assoc_of (htw : EtaleTensorPairTwistResolutionMul) (htri : EtaleTensorPairProductAssociative) (hext : EtaleTwistResolutionUniversalExtension)
    (hcc : EtaleCupProductNaturalInCoefficients) (ha0 : EtaleCochainCupAssociativeOfPairing) (hex : t_pa_tens_ex) (huniv : t_pa_tens_univ)
    (hpre : t_pa_precomp) (hid : t_pa_cpush_id) (hhtpy : t_pa_cpush_htpy) : t_pair_assoc := by
  intro q _ E i j l k₁ k₂ k e1 e2 e3 μ₁ μ₂ ν₁ ν₂ p1 p2 p3 p4 n m p s₁ s₂ s h₁ h₂ h₃ h₄ a b c
  obtain ⟨T, τ, hτ⟩ := hex (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  obtain ⟨T3, τ', hτ'⟩ := hex (ZMod q) T (res _ (tw q l))
  obtain ⟨u, hu⟩ := huniv (ZMod q) τ hτ μ₁
  obtain ⟨ρ, hρ⟩ := hpre (ZMod q) u μ₂
  obtain ⟨ν, hν⟩ := htri (ZMod q) τ τ' hτ hτ' ν₁ ν₂
  obtain ⟨w₁, hw₁⟩ := huniv (ZMod q) τ' hτ' ρ
  obtain ⟨w₂, hw₂⟩ := huniv (ZMod q) τ' hτ' ν
  obtain ⟨ri, -, -⟩ := hext q i
  obtain ⟨rj, fj, -⟩ := hext q j
  obtain ⟨rl, fl, -⟩ := hext q l
  have hT := htw q i j k₁ e1 _ _ ri rj fj τ hτ
  have ek : k₁ + l = k := by omega
  have hT3 := htw q k₁ l k ek _ _ hT rl fl τ' hτ'
  obtain ⟨-, -, huniq⟩ := hext q k
  obtain ⟨H⟩ := (huniq _ hT3).2 w₁ w₂ (by
    intro U ζ
    rw [hw₁, hw₂]
    simp only [HomologicalComplex.id_f, pa_sec_map_id]
    rw [hν U 0 0 0 0 0 0 (add_zero 0) (add_zero 0) (add_zero 0) (add_zero 0)]
    have r1 := hρ U 0 0 0 (add_zero 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) (resGen l ζ)
    simp only [HomologicalComplex.id_f, pa_sec_map_id] at r1
    have r2 := hu U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    simp only [HomologicalComplex.id_f, pa_sec_map_id] at r2
    erw [r1, r2, p1, p2, p3, p4])
  have L1 : μ₁.cup E h₁ a b = cpush _ u s₁ (τ.cup E h₁ a b) := by
    rw [hcc _ τ μ₁ (𝟙 _) (𝟙 _) u hu E h₁ a b, hid, hid]
  have L2 : ∀ y, μ₂.cup E h₂ (cpush _ u s₁ y) c = ρ.cup E h₂ y c := by
    intro y
    have := hcc _ ρ μ₂ u (𝟙 _) (𝟙 _) hρ E h₂ y c
    rw [hid, hid] at this
    exact this.symm
  have L3 : ∀ y, ρ.cup E h₂ y c = cpush _ w₁ s (τ'.cup E h₂ y c) := by
    intro y
    rw [hcc _ τ' ρ (𝟙 _) (𝟙 _) w₁ hw₁ E h₂ y c, hid, hid]
  have L4 : ∀ y, ν.cup E h₂ y c = cpush _ w₂ s (τ'.cup E h₂ y c) := by
    intro y
    rw [hcc _ τ' ν (𝟙 _) (𝟙 _) w₂ hw₂ E h₂ y c, hid, hid]
  rw [← ha0 _ τ ν ν₁ ν₂ hν E h₁ h₂ h₃ h₄ a b c, L1, L2, L3, L4, hhtpy _ E w₁ w₂ H]

end LateralTheory.EtaleFoundations
end

