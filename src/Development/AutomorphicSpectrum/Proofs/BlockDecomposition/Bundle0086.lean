module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi

variable {F : Type} [Field F] [NumberField F]

def LocMem (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (z : F) : Prop :=
  ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ ∃ y ∈ I, (s : F) * z = (y : F)

def cosetOff {ι : Type} (S : Finset (HeightOneSpectrum (𝓞 F))) (I : Ideal (𝓞 F)) (x0 : ι → F) : Set (ι → F) :=
  {x | ∀ v, v ∉ S → ∀ i, LocMem I v (x i - x0 i)}

def latCoset {ι : Type} (I : Ideal (𝓞 F)) (x0 : ι → F) : Set (ι → F) :=
  {x | ∀ i, ∃ y ∈ I, (y : F) = x i - x0 i}

def ballV (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : Set (Fv F v) :=
  {z | Valued.v z ≤ WithZero.exp (-(k : ℤ))}

def boxInd {ι : Type} (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (c y : ι → Fv F v) : ℝ :=
  if ∀ i, y i - c i ∈ ballV v k then 1 else 0

def term {ι : Type} (θ : ℝ →+* Ainf F) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (ι → Ainf F) → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ) (ε : ℝ) (x : ι → F) : ℝ :=
  φ (fun i => θ ε * algebraMap F (Ainf F) (x i)) * ∏ v ∈ S, ψ v fun i => algebraMap F (Fv F v) (x i)

end GlobalTheory.CompanionTheory.Equi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.CocProd

theorem tele {B : Type*} [CommRing B] (P : ℕ → B) (m : ℕ) :
    P 0 + ∑ i ∈ Finset.range m, (-1 : B) ^ (i + 1) * (P (i + 1) + P i) = (-1) ^ m * P m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    ring

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}
  (E : Frame (Φ := Φ) d) (σ : ∀ T : C, E.D ⟶ T)

theorem a_comp (i : Fin d) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    E.a σ i (φ ≫ ψ) = (Φ.A.map ψ).hom (E.a σ i φ) + E.a σ i ψ := by
  unfold Frame.a
  rw [E.add i (σ T ≫ φ ≫ ψ) (σ T' ≫ ψ) (σ T''), ← Category.assoc, E.nat]

def ga (i : Fin d) {n : ℕ} (s : ComposableArrows C n) (p q : Fin (n + 1)) (h : p ≤ q) :
    Φ.A.obj (s.obj (Fin.last n)) :=
  (Φ.A.map (s.map (homOfLE (Fin.le_last q)))).hom (E.a σ i (s.map (homOfLE h)))

theorem ga_add (i : Fin d) {n : ℕ} (s : ComposableArrows C n) (p q r : Fin (n + 1)) (h : p ≤ q) (h' : q ≤ r) :
    ga E σ i s p r (h.trans h') = ga E σ i s p q h + ga E σ i s q r h' := by
  unfold ga
  have e : s.map (homOfLE (h.trans h')) = s.map (homOfLE h) ≫ s.map (homOfLE h') := by
    rw [← s.map_comp]; rfl
  have e2 : s.map (homOfLE (Fin.le_last q)) = s.map (homOfLE h') ≫ s.map (homOfLE (Fin.le_last r)) := by
    rw [← s.map_comp]; rfl
  rw [e, a_comp, map_add (f := _), e2, Functor.map_comp]
  rfl

theorem ga_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (i : Fin d) {n : ℕ} (s : ComposableArrows C n)
    (p q : Fin (n + 1)) (h : p ≤ q) : ga E σ i s p q h ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
  have : E.a σ i (s.map (homOfLE h)) ∈ (Fil 1).S _ := by
    rw [hF.one]; exact E.mem i _ _
  exact (Fil _).map_mem _ (by simpa using this)

theorem prod_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {T : C} {j : ℕ} (f : Fin j → Φ.A.obj T)
    (hf : ∀ k, f k ∈ (Fil ((1 : ℕ) : ℤ)).S T) {q : ℕ} {x : Φ.A.obj T} (hx : x ∈ (Fil (q : ℤ)).S T) :
    (∏ k, f k) * x ∈ (Fil ((j + q : ℕ) : ℤ)).S T := by
  induction j with
  | zero =>
    simpa using hx
  | succ j ih =>
    rw [Fin.prod_univ_succ, mul_assoc]
    have := hF.mul 1 (j + q) T (hf 0) (ih (fun k => f k.succ) (fun k => hf k.succ))
    have e : 1 + (j + q) = j + 1 + q := by omega
    rwa [e] at this

theorem map_map {X Y Z : C} (g : X ⟶ Y) (f : Y ⟶ Z) (y : Φ.A.obj X) :
    (Φ.A.map f).hom ((Φ.A.map g).hom y) = (Φ.A.map (g ≫ f)).hom y := by
  simp

theorem face_form {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) =
      (∏ k : Fin j, ga E σ (I k) s (i.succAbove k.castSucc) (i.succAbove k.succ)
        ((Fin.strictMono_succAbove i).monotone (Fin.castSucc_lt_succ (i := k)).le)) *
      (Φ.A.map (toLast i s)).hom ((Φ.A.map (σ _)).hom x) := by
  unfold Frame.form
  rw [map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold ga
  rw [map_map]
  have e : (face i s).map (homOfLE (Fin.le_last k.succ)) ≫ toLast i s =
      s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [e]
  rfl

theorem sa_val {n : ℕ} (i : Fin (n + 1)) (m : Fin n) :
    ((i.succAbove m : Fin (n + 1)) : ℕ) = if (m : ℕ) < i then (m : ℕ) else m + 1 := by
  unfold Fin.succAbove
  split_ifs <;> simp_all [Fin.lt_def]

theorem ga_congr (i : Fin d) {n : ℕ} (s : ComposableArrows C n) {p q p' q' : Fin (n + 1)} (h : p ≤ q) (h' : p' ≤ q')
    (hp : (p : ℕ) = p') (hq : (q : ℕ) = q') : ga E σ i s p q h = ga E σ i s p' q' h' := by
  obtain rfl := Fin.ext hp
  obtain rfl := Fin.ext hq
  rfl

theorem sec_last {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) (hp : p = Fin.last n) :
    σ (s.obj p) ≫ s.map (homOfLE (Fin.le_last p)) = σ (s.obj (Fin.last n)) := by
  subst hp
  have : (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, s.map_id, Category.comp_id]

theorem d_form_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (j q : ℕ)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) (s : ComposableArrows C (j + 1)) :
    ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) ∈
      (Fil (((j : ℤ) + q) + 1)).S _ := by
  classical
  set u : Fin j → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun k =>
    ga E σ (I k) s k.castSucc.castSucc k.succ.castSucc (by rw [Fin.le_def]; simp) with hu
  set v : Fin j → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun k =>
    ga E σ (I k) s k.succ.castSucc k.succ.succ (by rw [Fin.le_def]; simp) with hv
  set P : ℕ → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun n => ∏ k : Fin j, if (k : ℕ) < n then u k else v k with hP
  set T : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    ∏ k : Fin j, ga E σ (I k) s (i.succAbove k.castSucc) (i.succAbove k.succ)
        ((Fin.strictMono_succAbove i).monotone (Fin.castSucc_lt_succ (i := k)).le) with hT
  set W : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    (Φ.A.map (toLast i s)).hom ((Φ.A.map (σ _)).hom x) with hW
  set Y := (Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom x with hY
  have hT0 : T 0 = P 0 := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Nat.not_lt_zero, if_false]
    refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp
  have hTl : T (Fin.last (j + 1)) = P j := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [k.2, if_true]
    refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp
  have hTi : ∀ i : Fin j, T i.succ.castSucc = P (i + 1) + P i := by
    intro i
    have hPa : P (i + 1) = u i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i + 1 then u k else v k) (Finset.mem_univ i)
      simp only [Nat.lt_add_one, if_true] at this
      exact this.symm
    have hPb : P i = v i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i then u k else v k) (Finset.mem_univ i)
      simp only [lt_irrefl, if_false] at this
      exact this.symm
    have hTa : T i.succ.castSucc = (u i + v i) * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => ga E σ (I k) s (i.succ.castSucc.succAbove k.castSucc)
        (i.succ.castSucc.succAbove k.succ) ((Fin.strictMono_succAbove _).monotone (Fin.castSucc_lt_succ (i := k)).le)) (Finset.mem_univ i)
      refine this.symm.trans ?_
      congr 1
      · rw [hu, hv]
        dsimp only
        rw [← ga_add]
        refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp only [sa_val, Fin.val_castSucc, Fin.val_succ] <;> split_ifs <;> omega
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
        split_ifs with h
        · refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp only [sa_val, Fin.val_castSucc, Fin.val_succ] <;> split_ifs <;> omega
        · refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp only [sa_val, Fin.val_castSucc, Fin.val_succ] <;> split_ifs <;> omega
    have hE : ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) =
        ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
      have : (k : ℕ) < i + 1 ↔ (k : ℕ) < i := by omega
      simp only [this]
    rw [hTa, hPa, hPb, hE]
    ring
  have hWY : ∀ i : Fin (j + 2), i ≠ Fin.last (j + 1) → W i = Y := by
    intro i hi
    have hi' : i.succAbove (Fin.last j) = Fin.last (j + 1) := by
      have h1 : (i : ℕ) ≠ j + 1 := fun h => hi (Fin.ext h)
      have h2 := i.2
      apply Fin.ext
      rw [sa_val]
      simp only [Fin.val_last]
      split_ifs <;> omega
    calc W i = (Φ.A.map (σ _ ≫ toLast i s)).hom x := map_map _ _ _
      _ = Y := by rw [show σ _ ≫ toLast i s = σ (s.obj (Fin.last (j + 1))) from sec_last E σ s _ hi']
  have hYW : Y - W (Fin.last (j + 1)) ∈ (Fil ((q : ℤ) + 1)).S _ := by
    have h := hc q (σ (s.obj (Fin.last (j + 1)))) (σ _ ≫ toLast (Fin.last (j + 1)) s) hx
    rwa [show W (Fin.last (j + 1)) = (Φ.A.map (σ _ ≫ toLast (Fin.last (j + 1)) s)).hom x from map_map _ _ _]
  have hsum : ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) =
      (-1) ^ j * (P j * (Y - W (Fin.last (j + 1)))) := by
    have hterm : ∀ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) =
        (-1) ^ (i : ℕ) * (T i * W i) := by
      intro i
      rw [face_form, zsmul_eq_mul]
      push_cast
      rfl
    rw [Finset.sum_congr rfl fun i _ => hterm i, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    have h0 : T (Fin.castSucc 0) = P 0 := hT0
    have hne0 : Fin.castSucc (0 : Fin (j + 1)) ≠ Fin.last (j + 1) := (Fin.castSucc_lt_last _).ne
    have hint : ∑ i : Fin j, (-1) ^ ((i.succ.castSucc : Fin (j + 2)) : ℕ) * (T i.succ.castSucc * W i.succ.castSucc) =
        (∑ m ∈ Finset.range j, (-1) ^ (m + 1) * (P (m + 1) + P m)) * Y := by
      rw [Finset.sum_mul, ← Fin.sum_univ_eq_sum_range (fun m => (-1) ^ (m + 1) * (P (m + 1) + P m) * Y) j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hTi, hWY _ (Fin.castSucc_lt_last _).ne]
      simp only [Fin.val_castSucc, Fin.val_succ]
      ring
    rw [hint, h0, hWY _ hne0, hTl]
    simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_last, pow_zero]
    linear_combination Y * tele P j
  rw [hsum]
  refine Ideal.mul_mem_left _ _ ?_
  have h := prod_mem hF (fun k : Fin j => if (k : ℕ) < j then u k else v k)
    (fun k => by
      split_ifs
      · exact ga_mem E σ hF _ s _ _ _
      · exact ga_mem E σ hF _ s _ _ _)
    (q := q + 1) (x := Y - W (Fin.last (j + 1))) (by push_cast; exact hYW)
  have e : ((j + (q + 1) : ℕ) : ℤ) = (j : ℤ) + q + 1 := by push_cast; ring
  rwa [e] at h

theorem rep_form {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame (Φ := Φ) d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) :
    ∃ c, Rep (Fil r) (Fil (r + 1)) (E.form σ I x) c := by
  subst hr
  have hmem : ∀ s : ComposableArrows C j, E.form σ I x s ∈ (Fil ((j : ℤ) + q)).S _ := by
    intro s
    have h := prod_mem hF _ (fun k => ga_mem E σ hF (I k) s k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)).le)
      ((Fil q).map_mem (σ _) hx)
    rw [Nat.cast_add] at h
    exact h
  let f : CH.Cn (sq (Fil ((j : ℤ) + q)) (Fil ((j : ℤ) + q + 1))) j := fun s => sqMk _ _ (E.form σ I x s) (hmem s)
  have hd : CH.d _ j f = 0 := by
    funext s
    apply Subtype.ext
    have h := Ideal.Quotient.eq_zero_iff_mem.2 (d_form_mem E σ hF hc j q I x hx s)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    refine Eq.trans ?_ h
    change Subtype.val (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • ((sq (Fil ((j : ℤ) + q)) (Fil ((j : ℤ) + q + 1))).map (toLast i s)).hom (f (face i s)) :
      sqM (Fil ((j : ℤ) + q)) (Fil ((j : ℤ) + q + 1)) _) = _
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    rfl
  exact ⟨_, f, hd, rfl, fun s => rfl⟩

end GlobalTheory.CompanionTheory.CocProd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicity
section
open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DetMonotone

private theorem exists_unitary_diagonal_eigenvalues_of_isHermitian {κ : Type} [Fintype κ] [DecidableEq κ] {A : Matrix κ κ ℂ} (hA : A.IsHermitian) :
    ∃ U : Matrix κ κ ℂ, U * star U = 1 ∧ star U * U = 1 ∧
      A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * star U := by
  refine ⟨(hA.eigenvectorUnitary : Matrix κ κ ℂ), Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2,
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, ?_⟩
  conv_lhs => rw [hA.spectral_theorem]
  rfl

theorem detMono : DetMono := by
  open ComplexOrder in (
    have one_le_re_det_lemma_2 : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] {Q : Matrix κ κ ℂ},
        Q.PosSemidef → 1 ≤ ((1 + Q).det).re := by
      intro κ _ _ Q hQ
      obtain ⟨U, h1, h2, hU⟩ := exists_unitary_diagonal_eigenvalues_of_isHermitian hQ.1
      have hsum : 1 + Q = U * diagonal (fun i => 1 + (hQ.1.eigenvalues i : ℂ)) * star U := by
        conv_lhs => rw [hU]
        rw [← diagonal_add, diagonal_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
      have hdet : (1 + Q).det = ∏ i, (1 + (hQ.1.eigenvalues i : ℂ)) := by
        rw [hsum, det_mul, det_mul, det_diagonal, mul_comm, ← mul_assoc, ← det_mul, h2, det_one, one_mul]
      rw [hdet, show (∏ i, (1 + (hQ.1.eigenvalues i : ℂ))) = ((∏ i, (1 + hQ.1.eigenvalues i) : ℝ) : ℂ) by
        push_cast; rfl, Complex.ofReal_re]
      calc (1 : ℝ) = ∏ _i : κ, (1 : ℝ) := by rw [Finset.prod_const_one]
        _ ≤ ∏ i, (1 + hQ.1.eigenvalues i) :=
          Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun i _ => le_add_of_nonneg_right (hQ.eigenvalues_nonneg i)
    intro κ _ _ X Y hX hP
    have hY : Y = X + (Y - X) := by abel
    by_cases h0 : X.det = 0
    · rw [h0, Complex.zero_re]
      have hnn := (hX.add hP).det_nonneg
      rw [← hY] at hnn
      exact (Complex.le_def.1 hnn).1
    · obtain ⟨U, h1, h2, hU⟩ := exists_unitary_diagonal_eigenvalues_of_isHermitian hX.1
      have hpos : ∀ i, 0 < hX.1.eigenvalues i := by
        intro i
        refine lt_of_le_of_ne (hX.eigenvalues_nonneg i) fun h => h0 ?_
        rw [hX.1.det_eq_prod_eigenvalues]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← h]; simp)
      set s : κ → ℂ := fun i => ((Real.sqrt (hX.1.eigenvalues i) : ℝ) : ℂ) with hs
      have hs0 : ∀ i, s i ≠ 0 := fun i => by
        simp only [hs, ne_eq, Complex.ofReal_eq_zero]
        exact (Real.sqrt_pos.2 (hpos i)).ne'
      have hss : ∀ i, s i * s i = (hX.1.eigenvalues i : ℂ) := fun i => by
        simp only [hs]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos i).le]
      have hstar : ∀ i, star (s i) = s i := fun i => by simp [hs]
      set B : Matrix κ κ ℂ := diagonal s * star U with hB
      set C : Matrix κ κ ℂ := U * diagonal (fun i => (s i)⁻¹) with hC
      have hCB : C * B = 1 := by
        rw [hB, hC, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal,
          show (fun i => (s i)⁻¹ * s i) = fun _ => (1 : ℂ) from funext fun i => inv_mul_cancel₀ (hs0 i),
          diagonal_one, Matrix.one_mul, h1]
      have hXB : X = Bᴴ * B := by
        rw [hB, conjTranspose_mul, diagonal_conjTranspose, star_eq_conjTranspose, conjTranspose_conjTranspose,
          show star s = s from funext hstar, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s),
          diagonal_mul_diagonal, show (fun i => s i * s i) = fun i => (hX.1.eigenvalues i : ℂ) from funext hss,
          ← Matrix.mul_assoc, ← star_eq_conjTranspose]
        exact hU
      have hsplit : Y = Bᴴ * (1 + Cᴴ * (Y - X) * C) * B := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← hXB, Matrix.mul_assoc, Matrix.mul_assoc, hCB,
          Matrix.mul_one, ← Matrix.mul_assoc, ← conjTranspose_mul, hCB, conjTranspose_one, Matrix.one_mul]
        abel
      have hQ : (Cᴴ * (Y - X) * C).PosSemidef := hP.conjTranspose_mul_mul_same C
      have hdX : X.det = Bᴴ.det * B.det := by rw [hXB, det_mul]
      clear_value B C
      have hdY : Y.det = (1 + Cᴴ * (Y - X) * C).det * X.det := by
        conv_lhs => rw [hsplit]
        rw [det_mul, det_mul, hdX]
        ring
      have hXnn := Complex.le_def.1 hX.det_nonneg
      have hQnn := Complex.le_def.1 (PosSemidef.one.add hQ).det_nonneg
      rw [hdY, Complex.mul_re, ← hXnn.2, ← hQnn.2]
      simp only [Complex.zero_im, mul_zero, sub_zero]
      have ha : 0 ≤ X.det.re := by simpa using hXnn.1
      exact le_mul_of_one_le_left ha (one_le_re_det_lemma_2 hQ))

end GlobalTheory.CompanionTheory.DetMonotone
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfSumApplyEqZero
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.EvalTensor

variable {G S V : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]

theorem eq_zero_of_sum_apply_eq_zero (σ : Representation ℂ G S) (π : Representation ℂ G V)
    (hirr : σ.IsIrreducible)
    (hschur : ∀ A : S →ₗ[ℂ] S, (∀ g s, A (σ g s) = σ g (A s)) → ∃ c : ℂ, A = c • LinearMap.id)
    {ι : Type} (b : ι → (S →ₗ[ℂ] V)) (hli : LinearIndependent ℂ b)
    (hb : ∀ i g s, b i (σ g s) = π g (b i s)) (J : Finset ι) :
    ∀ t : ι → S, ∑ j ∈ J, b j (t j) = 0 → ∀ j ∈ J, t j = 0 := by
  classical
  haveI : IsSimpleOrder (Subrepresentation σ) := hirr
  induction J using Finset.induction_on with
  | empty => intro t _ j hj; simp at hj
  | insert a J ha ih =>
    intro t ht
    rw [Finset.sum_insert ha] at ht
    have hta : t a = 0 := by
      by_contra hne
      let Φ : (J → S) →ₗ[ℂ] V := ∑ j : J, (b j.1).comp (LinearMap.proj j)
      have hΦ : ∀ f : J → S, Φ f = ∑ j : J, b j.1 (f j) := fun f => by
        simp [Φ, LinearMap.sum_apply]
      have hinj : Function.Injective Φ := by
        set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
        intro f hf
        rw [hΦ] at hf
        funext j
        have h0 := ih (fun i => if h : i ∈ J then f ⟨i, h⟩ else 0) (by
          rw [← Finset.sum_coe_sort J]
          simpa using hf) j.1 j.2
        simpa using h0
      have hequi : ∀ (g : G) (f : J → S), Φ (fun j => σ g (f j)) = π g (Φ f) := fun g f => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hΦ, hΦ, map_sum]
        exact Finset.sum_congr rfl fun j _ => hb j.1 g (f j)
      let W : Subrepresentation σ :=
        { toSubmodule := (LinearMap.range Φ).comap (b a)
          apply_mem_toSubmodule := by
            rintro g v ⟨f, hf⟩
            exact ⟨fun j => σ g (f j), by rw [hequi, hf, hb]⟩ }
      have hmem : t a ∈ W := by
        refine ⟨fun j => - t j.1, ?_⟩
        rw [hΦ]
        have h1 : ∑ j : J, b j.1 (- t j.1) = - ∑ j ∈ J, b j (t j) := by
          rw [← Finset.sum_coe_sort J, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ => map_neg _ _
        rw [h1]
        exact (eq_neg_of_add_eq_zero_left ht).symm ▸ rfl
      have htop : W = ⊤ := by
        rcases IsSimpleOrder.eq_bot_or_eq_top W with h | h
        · exfalso
          apply hne
          rw [h] at hmem
          exact hmem
        · exact h
      have hall : ∀ s, b a s ∈ LinearMap.range Φ := fun s => by
        have : s ∈ W := by rw [htop]; trivial
        exact this
      let e := LinearEquiv.ofInjective Φ hinj
      let B : S →ₗ[ℂ] (J → S) := e.symm.toLinearMap ∘ₗ (b a).codRestrict (LinearMap.range Φ) hall
      have hB : ∀ s, Φ (B s) = b a s := fun s => by
        have h1 : ((e (B s) : LinearMap.range Φ) : V) = Φ (B s) := LinearEquiv.ofInjective_apply _ _
        rw [← h1]
        simp [B]
      have hBc : ∀ g s, B (σ g s) = fun j => σ g (B s j) := fun g s => by
        apply hinj
        rw [hB, hequi, hB, hb]
      have hsc : ∀ j : J, ∃ c : ℂ, (LinearMap.proj j) ∘ₗ B = c • (LinearMap.id : S →ₗ[ℂ] S) := fun j =>
        hschur _ fun g s => by
          simp only [LinearMap.comp_apply, LinearMap.proj_apply]
          rw [hBc]
      choose c hc using hsc
      have hsum : b a = ∑ j : J, c j • b j.1 := by
        ext s
        rw [← hB, hΦ, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        have h1 : B s j = c j • s := by
          simpa using LinearMap.congr_fun (hc j) s
        rw [h1, map_smul, LinearMap.smul_apply]
      refine hli.notMem_span_image (s := (J : Set ι)) (x := a) (by simpa using ha) ?_
      rw [hsum]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j.1, j.2, rfl⟩)
    have hrest : ∑ j ∈ J, b j (t j) = 0 := by
      simpa [hta] using ht
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hta
    · exact ih t hrest j hj

theorem lift_flip_subtype_injective : ∀ {G S V : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G S) (π : Representation ℂ G V), σ.IsIrreducible → (∀ A : S →ₗ[ℂ] S, (∀ g s, A (σ g s) = σ g (A s)) → ∃ c : ℂ, A = c • LinearMap.id) → ∀ M : Submodule ℂ (S →ₗ[ℂ] V), (∀ f ∈ M, ∀ g s, f (σ g s) = π g (f s)) → Function.Injective (TensorProduct.lift (LinearMap.flip (M.subtype)) : S ⊗[ℂ] M →ₗ[ℂ] V) := by
  intro G S V _ _ _ _ _ σ π hirr hschur M hM
  classical
  let β := Module.Basis.ofVectorSpace ℂ M
  have hli : LinearIndependent ℂ (fun i => ((β i : M) : S →ₗ[ℂ] V)) :=
    β.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  let E := TensorProduct.equivFinsuppOfBasisRight (M := S) β
  have hxs : x = (E x).sum fun i s => s ⊗ₜ[ℂ] β i := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  have hsum : ∑ i ∈ (E x).support, ((β i : M) : S →ₗ[ℂ] V) (E x i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxs, Finsupp.sum, map_sum] at hx
    simpa using hx
  have h0 := eq_zero_of_sum_apply_eq_zero σ π hirr hschur _ hli
    (fun i g s => hM _ (β i).2 g s) (E x).support (fun i => E x i) hsum
  have hE : E x = 0 := by
    ext i
    by_cases hi : i ∈ (E x).support
    · simpa using h0 i hi
    · simpa using hi
  exact E.map_eq_zero_iff.1 hE

end GlobalTheory.CompanionTheory.EvalTensor
end

