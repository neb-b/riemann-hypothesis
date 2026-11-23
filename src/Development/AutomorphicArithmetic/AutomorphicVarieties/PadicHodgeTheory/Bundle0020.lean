module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTorusCoordsOfUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

section

variable {B : Type} [CommRing B]

private theorem triM_mul (t s : Fin 3 → Bˣ) (x y z x' y' z' : B) :
    triM t x y z * triM s x' y' z' =
      triM (fun i => t i * s i) (x + ((t 0 / t 1 : Bˣ) : B) * x') (y + ((t 1 / t 2 : Bˣ) : B) * y')
        (z + x * (((t 1 / t 2 : Bˣ) : B) * y') + ((t 0 / t 2 : Bˣ) : B) * z') := by
  have h1 := Units.inv_mul (t 1)
  have h2 := Units.inv_mul (t 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triM, Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv] <;>
    first
    | ring1
    | linear_combination (-((t 0 : B) * x' * (s 1 : B))) * h1
    | linear_combination (-((t 0 : B) * z' * (s 2 : B)) - (s 2 : B) * x * (t 1 : B) * y') * h2
    | linear_combination (-((t 1 : B) * y' * (s 2 : B))) * h2

private theorem triM_inj {t s : Fin 3 → Bˣ} {x y z x' y' z' : B} (h : triM t x y z = triM s x' y' z') :
    t = s ∧ x = x' ∧ y = y' ∧ z = z' := by
  have e : ∀ i j, triM t x y z i j = triM s x' y' z' i j := fun i j => by rw [h]
  have a0 := e 0 0
  have a1 := e 1 1
  have a2 := e 2 2
  have b1 := e 0 1
  have b2 := e 1 2
  have b3 := e 0 2
  simp [triM] at a0 a1 a2 b1 b2 b3
  have ht : t = s := by
    funext i
    fin_cases i
    · exact Units.ext a0
    · exact Units.ext a1
    · exact Units.ext a2
  subst ht
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa using congrArg (· * ((t 1)⁻¹ : Bˣ).val) b1
  · simpa using congrArg (· * ((t 2)⁻¹ : Bˣ).val) b2
  · simpa using congrArg (· * ((t 2)⁻¹ : Bˣ).val) b3

private theorem theta_triM {A : GL (Fin 3) B} {t : Fin 3 → Bˣ} {x y z : B}
    (h : (A : Matrix (Fin 3) (Fin 3) B) = triM t x y z) :
    (theta A : Matrix (Fin 3) (Fin 3) B) = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
  have h1 := Units.inv_mul (t 1)
  have h2 := Units.inv_mul (t 2)
  have key : triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) * ((theta A)⁻¹ : GL (Fin 3) B) = 1 := by
    rw [theta_inv_val, h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [triM, Jmat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.rev] <;>
      first
      | linear_combination y * h2
      | linear_combination z * h2 - x * y * h1
      | linear_combination x * h1
  calc (theta A : Matrix (Fin 3) (Fin 3) B)
      = 1 * (theta A : Matrix (Fin 3) (Fin 3) B) := (one_mul _).symm
    _ = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) * ((theta A)⁻¹ : GL (Fin 3) B) *
          (theta A : Matrix (Fin 3) (Fin 3) B) := by rw [key]
    _ = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
      rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

private theorem exists_triM (A : GL (Fin 3) B)
    (h : ∀ a b, wt a b < 0 → (A : Matrix (Fin 3) (Fin 3) B) a b = 0) :
    ∃ (t : Fin 3 → Bˣ) (x y z : B), (A : Matrix (Fin 3) (Fin 3) B) = triM t x y z := by
  have z10 := h 1 0 (by decide)
  have z20 := h 2 0 (by decide)
  have z21 := h 2 1 (by decide)
  have hd : IsUnit (A : Matrix (Fin 3) (Fin 3) B).det := Matrix.isUnits_det_units A
  rw [Matrix.det_fin_three, z10, z20, z21] at hd
  simp only [mul_zero, zero_mul, sub_zero, add_zero, zero_sub, neg_zero, IsUnit.mul_iff] at hd
  obtain ⟨⟨h0, h1⟩, h2⟩ := hd
  refine ⟨![h0.unit, h1.unit, h2.unit], (A : Matrix (Fin 3) (Fin 3) B) 0 1 * ↑h1.unit⁻¹,
    (A : Matrix (Fin 3) (Fin 3) B) 1 2 * ↑h2.unit⁻¹, (A : Matrix (Fin 3) (Fin 3) B) 0 2 * ↑h2.unit⁻¹, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [triM, z10, z20, z21, mul_assoc]

end

theorem UpperTheory.exists_torus_coords_of_unipotent :
    ∀ {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (h : B),
      2 * h = 1 → ∀ u : G →* GG (m := 3) (R := B), HasMult η u →
        (∀ g a b, wt a b < 0 → (u g).mat a b = 0) →
        ∃ (T : Tor η B) (β : G → B × B) (γ : G → B),
          T.Coord h β γ u ∧ (∀ g g', β (g * g') = β g + T.M1 g (β g')) ∧ T.IsGam h β γ := by
  intro G B _ _ η h h2 u hm hu
  have ex : ∀ g, ∃ (t : Fin 3 → Bˣ) (x y z : B), (u g).mat = triM t x y z :=
    fun g => exists_triM (u g).left (hu g)
  choose t x y z hA using ex
  have step : ∀ g g', ∃ (t' : Fin 3 → Bˣ) (x' y' z' : B),
      (u (g * g')).mat = triM (t g) (x g) (y g) (z g) * triM t' x' y' z' ∧
      ((η g = 1 ∧ t' = t g' ∧ x' = x g' ∧ y' = y g' ∧ z' = z g') ∨
       (η g = -1 ∧ t' = (fun i => (t g' i.rev)⁻¹) ∧ x' = -y g' ∧ y' = -x g' ∧ z' = x g' * y g' - z g')) := by
    intro g g'
    have hmul : (u (g * g')).mat = (u g).mat * (((sgnAct 3 B) (u g).right) (u g').left : Matrix (Fin 3) (Fin 3) B) := by
      rw [map_mul]
      show (((u g * u g').left : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) = _
      rw [SemidirectProduct.mul_left, Units.val_mul]
      rfl
    rw [hm g] at hmul
    rcases Int.units_eq_one_or (η g) with e | e
    · rw [e, sgnAct_one] at hmul
      exact ⟨_, _, _, _, by rw [hmul, hA g]; exact congrArg _ (hA g'), Or.inl ⟨e, rfl, rfl, rfl, rfl⟩⟩
    · rw [e, sgnAct_neg_one] at hmul
      exact ⟨_, _, _, _, by rw [hmul, hA g]; exact congrArg _ (theta_triM (hA g')), Or.inr ⟨e, rfl, rfl, rfl, rfl⟩⟩
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hab : ∀ g, ((t g 0 / t g 1 : Bˣ) : B) * ((t g 1 / t g 2 : Bˣ) : B) = ((t g 0 / t g 2 : Bˣ) : B) := by
    intro g
    rw [← Units.val_mul, div_mul_div_cancel]
  refine ⟨⟨t, ?_⟩, fun g => (x g, y g), fun g => z g - h * x g * y g, ⟨hm, fun g => ?_⟩, ?_, ?_⟩
  · intro g g' i
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨ht, -, -, -⟩ := triM_inj he
    rcases hc with ⟨e, rfl, -, -, -⟩ | ⟨e, rfl, -, -, -⟩
    · rw [ht]
      simp [e]
    · rw [ht]
      simp [e, hne]
  · rw [hA g]
    congr 1
    ring
  · intro g g'
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨-, hx, hy, -⟩ := triM_inj he
    rcases hc with ⟨e, -, rfl, rfl, -⟩ | ⟨e, -, rfl, rfl, -⟩
    · ext <;> simp [Tor.adjointSuperdiagRep_apply, e, hx, hy]
    · ext <;> simp [Tor.adjointSuperdiagRep_apply, e, hne, hx, hy]
  · intro g g'
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨-, hx, hy, hz⟩ := triM_inj he
    have hg := hab g
    simp only [Tor.χ2_apply, Tor.adjointSuperdiagRep_apply, omg]
    rcases hc with ⟨e, -, rfl, rfl, rfl⟩ | ⟨e, -, rfl, rfl, rfl⟩
    · simp only [e, if_true]
      rw [hx, hy, hz]
      push_cast
      linear_combination (-(x g * ((t g 1 / t g 2 : Bˣ) : B) * y g')) * h2 - (h * x g' * y g') * hg
    · simp only [e, hne, if_false]
      rw [hx, hy, hz]
      push_cast
      linear_combination (((t g 1 / t g 2 : Bˣ) : B) * x g * x g' - ((t g 0 / t g 2 : Bˣ) : B) * x g' * y g') * h2 - (h * x g' * y g') * hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUnipotentFromTorusCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private def triGL {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) : GL (Fin 3) B where
  val := triM t x y z
  inv := !![((t 0)⁻¹ : Bˣ), -x * ((t 0)⁻¹ : Bˣ), (x * y - z) * ((t 0)⁻¹ : Bˣ);
    0, ((t 1)⁻¹ : Bˣ), -y * ((t 1)⁻¹ : Bˣ); 0, 0, ((t 2)⁻¹ : Bˣ)]
  val_inv := by
    have h0 := (t 0).mul_inv
    have h1 := (t 1).mul_inv
    have h2 := (t 2).mul_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, Matrix.mul_apply, Fin.sum_univ_three, -Units.mul_inv, -Units.inv_mul] <;>
      first
        | assumption
        | linear_combination (-x) * h0
        | linear_combination (x * y - z) * h0 - x * y * h1
        | linear_combination (-y) * h1
  inv_val := by
    have h0 := (t 0).inv_mul
    have h1 := (t 1).inv_mul
    have h2 := (t 2).inv_mul
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, Matrix.mul_apply, Fin.sum_univ_three, -Units.mul_inv, -Units.inv_mul] <;>
      first
        | assumption
        | ring

private theorem triGL_val {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) :
    (triGL t x y z : Matrix (Fin 3) (Fin 3) B) = triM t x y z := rfl

private theorem triGL_congr {B : Type} [CommRing B] {t s : Fin 3 → Bˣ} {x y z x' y' z' : B}
    (ht : t = s) (hx : x = x') (hy : y = y') (hz : z = z') : triGL t x y z = triGL s x' y' z' := by
  subst ht hx hy hz
  rfl

private theorem theta_triGL {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) :
    theta (triGL t x y z) = triGL (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
  apply Units.ext
  rw [theta_val, triGL_val]
  have hinv : ((triGL t x y z)⁻¹ : GL (Fin 3) B).val =
      !![(((t 0)⁻¹ : Bˣ) : B), -x * (((t 0)⁻¹ : Bˣ) : B), (x * y - z) * (((t 0)⁻¹ : Bˣ) : B);
        0, (((t 1)⁻¹ : Bˣ) : B), -y * (((t 1)⁻¹ : Bˣ) : B); 0, 0, (((t 2)⁻¹ : Bˣ) : B)] := rfl
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jmat, triM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Fin.rev] <;> ring

private theorem triGL_mul {B : Type} [CommRing B] (t s : Fin 3 → Bˣ) (x y z x' y' z' : B) :
    triGL t x y z * triGL s x' y' z' = triGL (fun i => t i * s i)
      (x + ((t 0 / t 1 : Bˣ) : B) * x') (y + ((t 1 / t 2 : Bˣ) : B) * y')
      (z + ((t 0 / t 2 : Bˣ) : B) * z' + x * (((t 1 / t 2 : Bˣ) : B) * y')) := by
  apply Units.ext
  rw [Units.val_mul, triGL_val, triGL_val, triGL_val]
  have h1 := (t 1).inv_mul
  have h2 := (t 2).inv_mul
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, triM, div_eq_mul_inv, -Units.mul_inv, -Units.inv_mul] <;>
    first
      | linear_combination (-((t 0 : B) * x' * s 1)) * h1
      | linear_combination (-((t 1 : B) * y' * s 2)) * h2
      | linear_combination (-((t 0 : B) * z' * s 2 + x * t 1 * y' * s 2)) * h2

theorem UpperTheory.exists_unipotent_from_torus_coords :
    ∀ {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (T : Tor η B) (h : B), 2 * h = 1 →
      ∀ (β : G → B × B) (γ : G → B), (∀ g g', β (g * g') = β g + T.M1 g (β g')) →
        T.IsGam h β γ → ∃ u : G →* GG (m := 3) (R := B), T.Coord h β γ u := by
  intro G B _ _ η T h hh β γ hβ hγ
  let F : G → GG (m := 3) (R := B) := fun g =>
    ⟨triGL (T.t g) (β g).1 (β g).2 (γ g + h * (β g).1 * (β g).2), η g⟩
  have hmul : ∀ g g' : G, F (g * g') = F g * F g' := by
    intro g g'
    have hab : (((T.t g 0 / T.t g 2 : Bˣ)) : B) =
        ((T.t g 0 / T.t g 1 : Bˣ) : B) * ((T.t g 1 / T.t g 2 : Bˣ) : B) := by
      rw [← Units.val_mul, div_mul_div_cancel]
    have hb := hβ g g'
    have hc := hγ g g'
    apply SemidirectProduct.ext
    · simp only [F, SemidirectProduct.mul_left]
      rcases Int.units_eq_one_or (η g) with he | he
      · rw [he, sgnAct_one, triGL_mul]
        rw [Tor.adjointSuperdiagRep_apply, if_pos he] at hb
        rw [Tor.adjointSuperdiagRep_apply, if_pos he, Tor.χ2_apply, he] at hc
        apply triGL_congr
        · funext i
          rw [T.mul, if_pos he]
        · rw [hb]; rfl
        · rw [hb]; rfl
        · rw [hc, hb, hab]
          simp only [omg, Prod.fst_add, Prod.snd_add, Units.val_one, Int.cast_one, one_mul]
          linear_combination ((β g).1 * ((T.t g 1 / T.t g 2 : Bˣ) : B) * (β g').2) * hh
      · have hne : η g ≠ 1 := by rw [he]; decide
        rw [he, sgnAct_neg_one, theta_triGL, triGL_mul]
        rw [Tor.adjointSuperdiagRep_apply, if_neg hne] at hb
        rw [Tor.adjointSuperdiagRep_apply, if_neg hne, Tor.χ2_apply, he] at hc
        apply triGL_congr
        · funext i
          rw [T.mul, if_neg hne]
        · rw [hb]
          simp only [Prod.fst_add]
          ring
        · rw [hb]
          simp only [Prod.snd_add]
          ring
        · rw [hc, hb, hab]
          simp only [omg, Prod.fst_add, Prod.snd_add, Units.val_neg, Units.val_one, Int.cast_neg,
            Int.cast_one]
          linear_combination (((T.t g 0 / T.t g 1 : Bˣ) : B) * ((T.t g 1 / T.t g 2 : Bˣ) : B) *
            (β g').1 * (β g').2 - ((T.t g 1 / T.t g 2 : Bˣ) : B) * (β g).1 * (β g').1) * hh
    · simp only [F, SemidirectProduct.mul_right, map_mul]
  refine ⟨MonoidHom.mk' F hmul, ?_⟩
  exact Tor.Coord.mk (fun g => rfl) (fun g => rfl)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedCocycleFrobeniusValue
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.UnramifiedCocycles

variable {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]

private def SD (_ρ : Representation A G V) : Type := V × G

private instance instGroupSD (ρ : Representation A G V) : Group (SD ρ) where
  mul p q := (p.1 + ρ p.2 q.1, p.2 * q.2)
  one := (0, 1)
  inv p := (-(ρ p.2⁻¹ p.1), p.2⁻¹)
  mul_assoc p q r := by
    refine Prod.ext ?_ (mul_assoc p.2 q.2 r.2)
    change p.1 + ρ p.2 q.1 + ρ (p.2 * q.2) r.1 = p.1 + ρ p.2 (q.1 + ρ q.2 r.1)
    simp [add_assoc]
  one_mul p := by
    refine Prod.ext ?_ (one_mul p.2)
    change (0 : V) + ρ 1 p.1 = p.1
    simp
  mul_one p := by
    refine Prod.ext ?_ (mul_one p.2)
    change p.1 + ρ p.2 0 = p.1
    simp
  inv_mul_cancel p := by
    refine Prod.ext ?_ (inv_mul_cancel p.2)
    change -(ρ p.2⁻¹ p.1) + ρ p.2⁻¹ p.1 = 0
    simp

private instance instTopSD (ρ : Representation A G V) [TopologicalSpace G] [TopologicalSpace V] :
    TopologicalSpace (SD ρ) := inferInstanceAs (TopologicalSpace (V × G))

private theorem topGroup_SD (ρ : Representation A G V) [TopologicalSpace G] [TopologicalSpace V]
    [IsTopologicalGroup G] [IsTopologicalAddGroup V] (h : ContAction ρ) : IsTopologicalGroup (SD ρ) := by
  have hm : Continuous fun x : (V × G) × (V × G) => ((x.1.1 + ρ x.1.2 x.2.1, x.1.2 * x.2.2) : V × G) :=
    (continuous_fst.fst.add (h.comp (continuous_fst.snd.prodMk continuous_snd.fst))).prodMk
      (continuous_fst.snd.mul continuous_snd.snd)
  have hi : Continuous fun x : V × G => ((-(ρ x.2⁻¹ x.1), x.2⁻¹) : V × G) :=
    (h.comp (continuous_snd.inv.prodMk continuous_fst)).neg.prodMk continuous_snd.inv
  exact { continuous_mul := hm, continuous_inv := hi }

private def SDsub (ρ : Representation A G V) (L : AddSubgroup V) (hL : ∀ g, ∀ y ∈ L, ρ g y ∈ L) :
    Subgroup (SD ρ) where
  carrier := {p | p.1 ∈ L}
  mul_mem' := fun {p q} hp hq => L.add_mem hp (hL _ _ hq)
  one_mem' := L.zero_mem
  inv_mem' := fun {p} hp => L.neg_mem (hL _ _ hp)

private theorem all_of_closed [TopologicalSpace G] [IsTopologicalGroup G] {I : Subgroup G} {σ : G}
    (hd : (I ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤) (H : Subgroup G) (hH : IsClosed (H : Set G))
    (hI : I ≤ H) (hσ : σ ∈ H) (g : G) : g ∈ H := by
  have h1 : I ⊔ Subgroup.zpowers σ ≤ H := sup_le hI (Subgroup.zpowers_le.2 hσ)
  have h2 := Subgroup.topologicalClosure_minimal _ h1 hH
  rw [hd] at h2
  exact h2 (Subgroup.mem_top g)

private theorem exists_lattice {l : ℕ} [Fact l.Prime] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    [TopologicalSpace G] [CompactSpace G] (ρ : Representation A G V) (h : ContAction ρ) (x : V) :
    T2Space V ∧ TotallyDisconnectedSpace V ∧
      ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ x ∈ L ∧ ∀ g, ∀ y ∈ L, ρ g y ∈ L := by
  let e : V ≃ₗ[ℚ_[l]] (Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) := (Module.finBasis ℚ_[l] V).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm := LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
  let E : V ≃ₜ (Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) :=
    { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := he' }
  have hT2 : T2Space V := E.isEmbedding.t2Space
  have hTD : TotallyDisconnectedSpace V :=
    E.isEmbedding.isTotallyDisconnected_range.1 (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  refine ⟨hT2, hTD, ?_⟩
  have hρc : ∀ g : G, Continuous fun v : V => ρ g v :=
    fun g => h.comp (continuous_const.prodMk continuous_id)
  have hK : IsCompact (Set.range fun g : G => e (ρ g x)) :=
    isCompact_range (he.comp (h.comp (continuous_id.prodMk continuous_const)))
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hK.isBounded
  have hr1 : Set.range (fun g : G => e (ρ g x)) ⊆ Metric.closedBall 0 (max r 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  let M := (IsUltrametricDist.closedBall_openAddSubgroup (Fin (Module.finrank ℚ_[l] V) → ℚ_[l])
    (lt_of_lt_of_le one_pos (le_max_right r 1))).toAddSubgroup
  have hM : ∀ y, y ∈ M ↔ y ∈ Metric.closedBall (0 : Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) (max r 1) :=
    fun y => Iff.rfl
  let L : AddSubgroup V := ⨅ g : G, M.comap ((e.toLinearMap.toAddMonoidHom).comp (ρ g).toAddMonoidHom)
  have hL : ∀ v, v ∈ L ↔ ∀ g, e (ρ g v) ∈ Metric.closedBall 0 (max r 1) := by
    intro v
    simp only [L, AddSubgroup.mem_iInf, AddSubgroup.mem_comap, hM]
    rfl
  refine ⟨L, ?_, ?_, ?_⟩
  · have hcl : IsClosed (L : Set V) := by
      have : (L : Set V) = ⋂ g : G, (fun v => e (ρ g v)) ⁻¹' Metric.closedBall 0 (max r 1) := by
        ext v
        simp only [SetLike.mem_coe, hL, Set.mem_iInter, Set.mem_preimage]
      rw [this]
      exact isClosed_iInter fun g => Metric.isClosed_closedBall.preimage (he.comp (hρc g))
    have hsub : (L : Set V) ⊆ E ⁻¹' Metric.closedBall 0 (max r 1) := by
      intro v hv
      have := (hL v).1 hv 1
      simpa [E] using this
    exact (E.isCompact_preimage.2 (isCompact_closedBall _ _)).of_isClosed_subset hcl hsub
  · exact (hL x).2 fun g => hr1 ⟨g, rfl⟩
  · intro g y hy
    refine (hL _).2 fun k => ?_
    have := (hL y).1 hy (k * g)
    simpa [map_mul] using this

end UpperTheory.V.Loc.UnramifiedCocycles

open UpperTheory.V.Loc.UnramifiedCocycles in
theorem UpperTheory.V.Loc.existsUnique_unramified_cocycle_frobenius_value :
    ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A (GQ v) V), ContAction ρ → (∀ g ∈ Iq v, ρ g = 1) → ∀ σ : GQ v, UpperTheory.V.Loc.IsFrob σ → ∀ x : V, ∃! c : GQ v → V, c ∈ Z1 ρ ∧ (∀ g ∈ Iq v, c g = 0) ∧ c σ = x := by
  intro v l _ _ A _ _ V _ _ _ _ _ _ _ _ _ ρ hc hI σ hσ x
  obtain ⟨hT2, hTD, L, hLc, hxL, hLs⟩ := exists_lattice (l := l) ρ hc x
  haveI : IsTopologicalGroup (SD ρ) := topGroup_SD ρ hc
  haveI : T2Space (SD ρ) := inferInstanceAs (T2Space (V × GQ v))
  haveI : TotallyDisconnectedSpace (SD ρ) := inferInstanceAs (TotallyDisconnectedSpace (V × GQ v))
  have hS : IsCompact ((SDsub ρ L hLs : Subgroup (SD ρ)) : Set (SD ρ)) := by
    have h0 : IsCompact ((L : Set V) ×ˢ (Set.univ : Set (GQ v))) := hLc.prod isCompact_univ
    have e0 : ((SDsub ρ L hLs : Subgroup (SD ρ)) : Set (SD ρ)) =
        ((L : Set V) ×ˢ (Set.univ : Set (GQ v)) : Set (V × GQ v)) := by
      ext p
      exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
    rw [e0]
    exact h0
  haveI : CompactSpace (SDsub ρ L hLs) := isCompact_iff_compactSpace.1 hS
  obtain ⟨f, hfc, hf1, hfσ⟩ := frobFree σ hσ (SDsub ρ L hLs) ⟨((x, σ) : V × GQ v), hxL⟩
  have hfv : Continuous fun g => ((f g : SD ρ)) := continuous_subtype_val.comp hfc
  have hmul : ∀ g h, ((f (g * h) : SD ρ)) = (f g : SD ρ) * (f h : SD ρ) := fun g h => by
    rw [map_mul]
    rfl
  let k : GQ v → GQ v := fun g => ((f g : SD ρ)).2
  have hk1 : k 1 = 1 := by
    show ((f 1 : SD ρ)).2 = 1
    rw [map_one]
    rfl
  have hkm : ∀ a b, k (a * b) = k a * k b := fun a b => by
    show ((f (a * b) : SD ρ)).2 = _
    rw [hmul]
    rfl
  have hki : ∀ a, k a⁻¹ = (k a)⁻¹ := fun a => by
    have : k a⁻¹ * k a = 1 := by rw [← hkm, inv_mul_cancel, hk1]
    exact eq_inv_of_mul_eq_one_left this
  have hkc : Continuous k := continuous_snd.comp hfv
  have hgw : ∀ w : V, Continuous fun g : GQ v => ρ g w := fun w => hc.comp (continuous_id.prodMk continuous_const)
  have happ : ∀ (g : GQ v) (w : V), ρ g (ρ g⁻¹ w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have happ' : ∀ (g : GQ v) (w : V), ρ g⁻¹ (ρ g w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let H : Subgroup (GQ v) :=
    { carrier := {g | ∀ w, ρ (k g) w = ρ g w}
      one_mem' := fun w => by simp [hk1]
      mul_mem' := fun {a b} ha hb w => by
        simp only [Set.mem_setOf_eq] at ha hb
        rw [hkm, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha w => by
        simp only [Set.mem_setOf_eq] at ha
        rw [hki]
        calc ρ (k a)⁻¹ w = ρ (k a)⁻¹ (ρ a (ρ a⁻¹ w)) := by rw [happ]
          _ = ρ (k a)⁻¹ (ρ (k a) (ρ a⁻¹ w)) := by rw [ha]
          _ = ρ a⁻¹ w := happ' _ _ }
  have hH : IsClosed (H : Set (GQ v)) := by
    have e1 : (H : Set (GQ v)) = ⋂ w : V, {g | ρ (k g) w = ρ g w} := by
      ext g
      simp [H]
    rw [e1]
    exact isClosed_iInter fun w => isClosed_eq ((hgw w).comp hkc) (hgw w)
  have hIH : Iq v ≤ H := fun g hg w => by
    show ρ ((f g : SD ρ)).2 w = ρ g w
    rw [hf1 g hg, hI g hg]
    show ρ (1 : GQ v) w = (1 : Module.End A V) w
    simp
  have hσH : σ ∈ H := fun w => by
    show ρ ((f σ : SD ρ)).2 w = ρ σ w
    rw [hfσ]
  have hk : ∀ g w, ρ (k g) w = ρ g w := fun g => all_of_closed (frobDense σ hσ) H hH hIH hσH g
  let c : GQ v → V := fun g => ((f g : SD ρ)).1
  have ccont : Continuous c := continuous_fst.comp hfv
  have cco : ∀ g h, c (g * h) = c g + ρ g (c h) := fun g h => by
    show ((f (g * h) : SD ρ)).1 = ((f g : SD ρ)).1 + ρ g ((f h : SD ρ)).1
    rw [hmul]
    exact congrArg (((f g : SD ρ)).1 + ·) (hk g _)
  have cI : ∀ g ∈ Iq v, c g = 0 := fun g hg => by
    show ((f g : SD ρ)).1 = 0
    rw [hf1 g hg]
    rfl
  have cσ : c σ = x := by
    show ((f σ : SD ρ)).1 = x
    rw [hfσ]
  have h1 : ∀ d : GQ v → V, (∀ g h, d (g * h) = d g + ρ g (d h)) → d 1 = 0 := fun d hd => by
    have := hd 1 1
    simpa using this
  have hinv : ∀ d : GQ v → V, (∀ g h, d (g * h) = d g + ρ g (d h)) → ∀ g, d g⁻¹ = -(ρ g⁻¹ (d g)) :=
    fun d hd g => by
      have := hd g⁻¹ g
      rw [inv_mul_cancel, h1 d hd] at this
      exact eq_neg_of_add_eq_zero_left this.symm
  refine ⟨c, ⟨⟨ccont, cco⟩, cI, cσ⟩, ?_⟩
  rintro c' ⟨hZ, hc'I, hc'σ⟩
  obtain ⟨c'cont, c'co⟩ : Continuous c' ∧ ∀ g h, c' (g * h) = c' g + ρ g (c' h) := hZ
  let H' : Subgroup (GQ v) :=
    { carrier := {g | c' g = c g}
      one_mem' := by
        show c' 1 = c 1
        rw [h1 c' c'co, h1 c cco]
      mul_mem' := fun {a b} ha hb => by
        show c' (a * b) = c (a * b)
        rw [c'co, cco, show c' a = c a from ha, show c' b = c b from hb]
      inv_mem' := fun {a} ha => by
        show c' a⁻¹ = c a⁻¹
        rw [hinv c' c'co, hinv c cco, show c' a = c a from ha] }
  have hH' : IsClosed (H' : Set (GQ v)) := isClosed_eq c'cont ccont
  have hIH' : Iq v ≤ H' := fun g hg => by
    show c' g = c g
    rw [hc'I g hg, cI g hg]
  have hσH' : σ ∈ H' := by
    show c' σ = c σ
    rw [hc'σ, cσ]
  funext g
  exact all_of_closed (frobDense σ hσ) H' hH' hIH' hσH' g
end

