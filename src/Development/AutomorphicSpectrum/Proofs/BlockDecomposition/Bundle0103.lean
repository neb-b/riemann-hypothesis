module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0095
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0092
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0094
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0086
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0099
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteProductDifferenceBoundStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_product_difference_bound : ∀ (V : Type) (a : V → ℝ) (A U : Finset V), A ⊆ U → |∏ v ∈ U, a v - ∏ v ∈ A, a v| ≤ ∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, |a v - 1| := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.abs_prod_sub_prod_le_sum_powerset | exact GlobalTheory.CompanionTheory.Mass.MeanV.abs_prod_sub_prod_le_sum_powerset | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.abs_prod_sub_prod_le_sum_powerset <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GLTransitiveNonzeroVectors
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

namespace GlobalTheory.CompanionTheory.TyFin.RowTrans

theorem exists_linearEquiv_apply_eq_of_ne_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : ∃ e : V ≃ₗ[K] V, e x = y := by
  have hx1 : (LinearEquiv.toSpanNonzeroSingleton K V x hx).symm
      ⟨x, Submodule.mem_span_singleton_self x⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton K V x hx).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton K V y hy))
  refine ⟨g, ?_⟩
  have h := hg ⟨x, Submodule.mem_span_singleton_self x⟩
  rw [LinearEquiv.trans_apply, hx1, LinearEquiv.toSpanNonzeroSingleton_one] at h
  exact h.symm

theorem gl_transitive_rows : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ)
    (r r' : Fin j → K), r ≠ 0 → r' ≠ 0 →
    ∃ g : GL (Fin j) K, Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K) = r' := by
  intro K _ _ _ j r r' hr hr'
  obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.TyFin.RowTrans.exists_linearEquiv_apply_eq_of_ne_zero (K := K) hr hr'
  have h1 : (e.symm : (Fin j → K) →ₗ[K] Fin j → K) ∘ₗ (e : (Fin j → K) →ₗ[K] Fin j → K) =
      LinearMap.id := LinearMap.ext fun v => by simp
  have h2 : (e : (Fin j → K) →ₗ[K] Fin j → K) ∘ₗ (e.symm : (Fin j → K) →ₗ[K] Fin j → K) =
      LinearMap.id := LinearMap.ext fun v => by simp
  refine ⟨⟨(LinearMap.toMatrix' (e : (Fin j → K) →ₗ[K] Fin j → K)).transpose,
    (LinearMap.toMatrix' (e.symm : (Fin j → K) →ₗ[K] Fin j → K)).transpose, ?_, ?_⟩, ?_⟩
  · rw [← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp, h1, LinearMap.toMatrix'_id,
      Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_id,
      Matrix.transpose_one]
  · change Matrix.vecMul r (LinearMap.toMatrix' (e : (Fin j → K) →ₗ[K] Fin j → K)).transpose = r'
    rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
    exact he

end GlobalTheory.CompanionTheory.TyFin.RowTrans
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InitialObjectAugmentedResolution
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

noncomputable section

namespace GlobalTheory.CompanionTheory.InitialCoh

open GlobalTheory.CatH (face toLast)

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T₀ : C}

def pre (h : Limits.IsInitial T₀) {n : ℕ} (s : ComposableArrows C n) : ComposableArrows C (n + 1) :=
  s.precomp (h.to s.left)

theorem pre_map (h : Limits.IsInitial T₀) {n : ℕ} (s : ComposableArrows C n) (a b : Fin (n + 1)) (hab : a ≤ b) :
    (pre h s).map (homOfLE (Fin.succ_le_succ_iff.2 hab)) = s.map (homOfLE hab) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  rfl

theorem map_homOfLE_source_eq {m : ℕ} (s : ComposableArrows C m) {a a' b : Fin (m + 1)} (hab : a ≤ b) (hab' : a' ≤ b) (e : a = a') :
    s.map (homOfLE hab) = eqToHom (congrArg s.obj e) ≫ s.map (homOfLE hab') := by
  subst e
  simp

theorem val_congr (F : C ⥤ ModuleCat.{w} R) {m : ℕ} (y : Cn F m) {a b : ComposableArrows C m} (e : a = b) {X : C}
    (φ : a.obj (Fin.last m) ⟶ X) (ψ : b.obj (Fin.last m) ⟶ X)
    (hφ : φ = eqToHom (congrArg (fun c : ComposableArrows C m => c.obj (Fin.last m)) e) ≫ ψ) :
    (F.map φ).hom (y a) = (F.map ψ).hom (y b) := by
  subst e
  simp only [eqToHom_refl, Category.id_comp] at hφ
  rw [hφ]

theorem hom_from_initial (h : Limits.IsInitial T₀) {X Y : C} (e : X = T₀) (a b : X ⟶ Y) : a = b := by
  subst e
  exact h.hom_ext a b

theorem whisker_congr {k l : ℕ} (a b : Fin (k + 1) ⥤ Fin (l + 1)) (e : ∀ i, a.obj i = b.obj i) (P : ComposableArrows C l) :
    a ⋙ P = b ⋙ P := by
  have : a = b := CategoryTheory.Functor.ext e (fun _ _ _ => Subsingleton.elim _ _)
  rw [this]

theorem face_zero_pre (h : Limits.IsInitial T₀) {n : ℕ} (s : ComposableArrows C n) : face 0 (pre h s) = s :=
  whisker_congr _ (Fin.succFunctor _) (fun i => by simp) (pre h s)

theorem face_face {m : ℕ} (P : ComposableArrows C (m + 2)) (a a' : Fin (m + 2)) (b b' : Fin (m + 3))
    (e : ∀ x, b.succAbove (a.succAbove x) = b'.succAbove (a'.succAbove x)) : face a (face b P) = face a' (face b' P) :=
  whisker_congr ((Fin.succAboveOrderEmb a).monotone.functor ⋙ (Fin.succAboveOrderEmb b).monotone.functor)
    ((Fin.succAboveOrderEmb a').monotone.functor ⋙ (Fin.succAboveOrderEmb b').monotone.functor) e P

theorem eq_of_face_zero (h : Limits.IsInitial T₀) {n : ℕ} {P Q : ComposableArrows C (n + 1)} (h0 : P.obj 0 = T₀) (h1 : Q.obj 0 = T₀)
    (e : face 0 P = face 0 Q) : P = Q := by
  refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
  · refine Fin.cases (h0.trans h1.symm) (fun j => ?_) i
    have := Functor.congr_obj e j
    simpa [face] using this
  · cases i with
    | zero => exact hom_from_initial h h0 _ _
    | succ i =>
      exact Functor.congr_hom e (homOfLE (Nat.le_succ i) : (⟨i, by omega⟩ : Fin (n + 1)) ⟶ ⟨i + 1, by omega⟩)

theorem face_succ_pre (h : Limits.IsInitial T₀) {n : ℕ} (s : ComposableArrows C (n + 1)) (i : Fin (n + 2)) :
    face i.succ (pre h s) = pre h (face i s) := by
  refine eq_of_face_zero h ?_ rfl ?_
  · change (pre h s).obj (i.succ.succAbove 0) = T₀
    rw [Fin.succ_succAbove_zero]
    rfl
  · rw [face_zero_pre, face_face (pre h s) 0 i i.succ 0 (fun x => by simp [Fin.succ_succAbove_succ]), face_zero_pre]

theorem val_zero (F : C ⥤ ModuleCat.{w} R) (h : Limits.IsInitial T₀) {n : ℕ} (y : Cn F n) (s : ComposableArrows C n) :
    (F.map (toLast 0 (pre h s))).hom (y (face 0 (pre h s))) = y s := by
  have e : (0 : Fin (n + 2)).succAbove (Fin.last n) = Fin.last (n + 1) := by simp
  have := val_congr F y (face_zero_pre h s) (toLast 0 (pre h s)) (𝟙 _)
    ((map_homOfLE_source_eq (pre h s) _ le_rfl e).trans
      (congrArg (fun g => eqToHom _ ≫ g) ((pre h s).map_id (Fin.last (n + 1)))))
  refine this.trans ?_
  rw [F.map_id]
  rfl

theorem val_succ (F : C ⥤ ModuleCat.{w} R) (h : Limits.IsInitial T₀) {n : ℕ} (y : Cn F (n + 1))
    (s : ComposableArrows C (n + 1)) (i : Fin (n + 2)) :
    (F.map (toLast i.succ (pre h s))).hom (y (face i.succ (pre h s))) =
      (F.map (toLast i s)).hom (y (pre h (face i s))) := by
  have e : i.succ.succAbove (Fin.last (n + 1)) = (i.succAbove (Fin.last n)).succ := by
    rw [← Fin.succ_last, Fin.succ_succAbove_succ]
  exact val_congr F y (face_succ_pre h s i) (toLast i.succ (pre h s)) (toLast i s)
    ((map_homOfLE_source_eq (pre h s) _ (Fin.succ_le_succ_iff.2 (Fin.le_last _)) e).trans
      (congrArg (fun g => eqToHom _ ≫ g) (pre_map h s _ _ (Fin.le_last _))))

def con (F : C ⥤ ModuleCat.{w} R) (h : Limits.IsInitial T₀) (n : ℕ) (y : Cn F (n + 1)) : Cn F n := fun s => y (pre h s)

theorem d_con (F : C ⥤ ModuleCat.{w} R) (h : Limits.IsInitial T₀) (n : ℕ) (y : Cn F (n + 1)) (hy : d F (n + 1) y = 0) :
    d F n (con F h n y) = y := by
  funext s
  have key : ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i (pre h s))).hom (y (face i (pre h s))) = 0 :=
    congrFun hy (pre h s)
  rw [Fin.sum_univ_succ] at key
  simp only [val_succ, Fin.val_succ, Fin.val_zero, pow_zero, one_smul, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib] at key
  rw [val_zero] at key
  exact (add_neg_eq_zero.1 key).symm

theorem resUpTo_one (F : C ⥤ ModuleCat.{w} R) (T₀ : C) (h : Limits.IsInitial T₀) :
    (cx F).ResUpTo 1 (aug F fun T => (F.map (h.to T)).hom) := by
  have hid : h.to T₀ = 𝟙 T₀ := h.hom_ext _ _
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun n y hy => ⟨con F h n y, ?_⟩⟩
  · funext s
    change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom ((F.map (h.to ((face i s).obj (Fin.last 0)))).hom x) = 0
    have e : ∀ i : Fin 2, (F.map (toLast i s)).hom ((F.map (h.to ((face i s).obj (Fin.last 0)))).hom x) =
        (F.map (h.to (s.obj (Fin.last 1)))).hom x := fun i => by
      rw [← ModuleCat.comp_apply, ← F.map_comp, h.hom_ext (h.to _ ≫ toLast i s) (h.to _)]
    simp only [e]
    simp [Fin.sum_univ_two]
  · have : (F.map (h.to T₀)).hom x = 0 := congrFun hx (ComposableArrows.mk₀ T₀)
    rw [hid] at this
    simpa using this
  · refine ⟨y (ComposableArrows.mk₀ T₀), funext fun s => ?_⟩
    have key : ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i (pre h s))).hom (y (face i (pre h s))) = 0 :=
      congrFun hy (pre h s)
    have e1 : face 1 (pre h s) = ComposableArrows.mk₀ T₀ := ComposableArrows.ext₀ rfl
    have t1 : (F.map (toLast 1 (pre h s))).hom (y (face 1 (pre h s))) =
        (F.map (h.to (s.obj (Fin.last 0)))).hom (y (ComposableArrows.mk₀ T₀)) :=
      val_congr F y e1 _ _ (hom_from_initial h rfl _ _)
    rw [Fin.sum_univ_two, t1] at key
    have t0 := val_zero F h y s
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at key
    rw [t0] at key
    rw [one_smul]
    exact (add_neg_eq_zero.1 key).symm
  · rw [one_smul]
    exact d_con F h n y hy

end GlobalTheory.CompanionTheory.InitialCoh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCosetScaledRiemannSum
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Equi.LatSum

section Abstract

variable {A O Q ι : Type} [AddCommGroup A] [AddCommGroup O] [Fintype ι] [Fintype Q]

def reps (j : O →+ A) (rep : Q → O) : Finset (ι → A) :=
  Finset.univ.image fun (c : ι → Q) (i : ι) => j (rep (c i))

theorem card_reps (j : O →+ A) (hj : Function.Injective j) (q : O → Q) (rep : Q → O)
    (hrep : ∀ c, q (rep c) = c) :
    (reps (ι := ι) j rep).card = Fintype.card Q ^ Fintype.card ι := by
  unfold reps
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fun]
  intro c c' h
  funext i
  have h1 : j (rep (c i)) = j (rep (c' i)) := congrFun h i
  have h2 := congrArg q (hj h1)
  rwa [hrep, hrep] at h2

theorem tile_pi (H : AddSubgroup O) (j : O →+ A) (hj : Function.Injective j) (q : O → Q) (rep : Q → O)
    (hrep : ∀ c, q (rep c) = c) (hq : ∀ a b, q a = q b ↔ a - b ∈ H) (D₀ : Set A)
    (hD : ∀ y : A, ∃! a : O, y - j a ∈ D₀) (y : ι → A) :
    ∃! p : (ι → A) × (ι → A), p.1 ∈ reps (ι := ι) j rep ∧
      p.2 ∈ AddSubgroup.pi Set.univ (fun _ : ι => H.map j) ∧
      y - p.1 - p.2 ∈ Set.pi Set.univ (fun _ : ι => D₀) := by
  choose a ha hau using fun i => hD (y i)
  refine ⟨(fun i => j (rep (q (a i))), fun i => j (a i - rep (q (a i)))), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Finset.mem_image.2 ⟨fun i => q (a i), Finset.mem_univ _, rfl⟩
  · intro i _
    refine AddSubgroup.mem_map.2 ⟨a i - rep (q (a i)), ?_, rfl⟩
    exact (hq _ _).1 (hrep _).symm
  · intro i _
    have : y i - j (rep (q (a i))) - j (a i - rep (q (a i))) = y i - j (a i) := by
      rw [map_sub]; abel
    simpa [this] using ha i
  · rintro ⟨p₁, p₂⟩ ⟨h1, h2, h3⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h1
    have hl : ∀ i, ∃ l ∈ H, j l = p₂ i := fun i => by
      obtain ⟨l, hl, e⟩ := AddSubgroup.mem_map.1 (h2 i (Set.mem_univ i))
      exact ⟨l, hl, e⟩
    choose l hlH hlj using hl
    have hai : ∀ i, rep (c i) + l i = a i := fun i => by
      refine hau i _ ?_
      have h4 := h3 i (Set.mem_univ i)
      have h5 : y i - j (rep (c i) + l i) = (y - (fun i => j (rep (c i))) - p₂) i := by
        simp only [Pi.sub_apply, map_add (f := _), hlj]; abel
      show y i - j (rep (c i) + l i) ∈ D₀
      rw [h5]; exact h4
    have hc : ∀ i, q (a i) = c i := fun i => by
      have h6 : q (a i) = q (rep (c i)) := (hq _ _).2 (by rw [← hai i]; simpa using hlH i)
      rwa [hrep] at h6
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show j (rep (c i)) = j (rep (q (a i)))
      rw [hc]
    · show p₂ i = j (a i - rep (q (a i)))
      rw [hc, ← hai i, add_sub_cancel_left, hlj]

end Abstract

def scal {R : Type} (ι : Type) [CommRing R] (t : R) : (ι → R) →+ (ι → R) where
  toFun y i := t * y i
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp [mul_add]

end GlobalTheory.CompanionTheory.Equi.LatSum


open GlobalTheory.CompanionTheory.Equi.LatSum in
theorem GlobalTheory.CompanionTheory.Equi.lat_sum : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ li : Measure (Ainf F), IsStdInf li → ∀ (ι : Type) [Fintype ι] (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ (x0 : ι → F) (φ : (ι → Ainf F) → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun x : latCoset I x0 => φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) ∧ Tendsto (fun ε : ℝ => ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x : latCoset I x0, φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) (𝓝[>] 0) (𝓝 (((Ideal.absNorm I : ℝ) ^ Fintype.card ι)⁻¹ * ∫ y, φ y ∂(Measure.pi fun _ => li))) := by
  intro F _ _ hF θ hθ li hli ι _ I hI x0 φ hφ hφs
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : li.IsAddHaarMeasure := hli.1
  obtain ⟨D₀, K₀, hDm, hK, hDK, hD1, htile⟩ := _root_.GlobalTheory.CompanionTheory.Equi.exists_bounded_infDomain F hF li hli
  have hg : Function.Injective (algebraMap F (Ainf F)) := (algebraMap F (Ainf F)).injective
  let j : 𝓞 F →+ Ainf F := ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom
  have hj : Function.Injective j := hg.comp (IsFractionRing.injective (𝓞 F) F)
  let H : AddSubgroup (𝓞 F) := I.toAddSubgroup
  haveI hfin : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  let rep : 𝓞 F ⧸ I → 𝓞 F := Function.surjInv Ideal.Quotient.mk_surjective
  have hrep : ∀ c, Ideal.Quotient.mk I (rep c) = c := Function.surjInv_eq _
  have hq : ∀ a b, Ideal.Quotient.mk I a = Ideal.Quotient.mk I b ↔ a - b ∈ H := fun a b => Ideal.Quotient.eq
  let Λ : AddSubgroup (ι → Ainf F) := AddSubgroup.pi Set.univ (fun _ : ι => H.map j)
  haveI : Countable (𝓞 F) := (RingOfIntegers.basis F).equivFun.toEquiv.injective.countable
  haveI : Countable (H.map j) := by
    have : (↑(H.map j) : Set (Ainf F)).Countable := (Set.to_countable (H : Set (𝓞 F))).image j
    exact this.to_subtype
  haveI : Countable Λ := by
    refine Function.Injective.countable (f := fun (l : Λ) (i : ι) => (⟨l.1 i, l.2 i (Set.mem_univ i)⟩ : H.map j)) ?_
    intro l l' h
    exact Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i))
  have hcard : ((reps (ι := ι) j rep).card : ℝ) = (Ideal.absNorm I : ℝ) ^ Fintype.card ι := by
    rw [card_reps j hj (Ideal.Quotient.mk I) rep hrep, Nat.cast_pow, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  let T : ℝ → (ι → Ainf F) →+ (ι → Ainf F) := fun ε => scal ι (θ ε)
  have hjoint : Continuous fun p : ℝ × (ι → Ainf F) => T p.1 p.2 :=
    continuous_pi fun i => (hθ.comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)
  have hθ0 : θ 0 = 0 := map_zero θ
  have key := _root_.GlobalTheory.CompanionTheory.RiemannCore.main (ι → Ainf F) (Measure.pi fun _ => li) Λ (Set.pi Set.univ fun _ => D₀)
    (Set.pi Set.univ fun _ => K₀) (reps (ι := ι) j rep) T (Module.finrank ℚ F * Fintype.card ι)
    (MeasurableSet.univ_pi fun _ => hDm) (isCompact_univ_pi fun _ => hK)
    (Set.pi_mono fun _ _ => hDK)
    (by rw [Measure.pi_pi]; simp [hD1])
    (fun y => tile_pi H j hj (Ideal.Quotient.mk I) rep hrep hq D₀ htile y)
    (fun ε _ => continuous_pi fun i => continuous_const.mul (continuous_apply i))
    (fun ε hε y => by
      have h1 : θ ε⁻¹ * θ ε = 1 := by rw [← map_mul, inv_mul_cancel₀ hε.ne', map_one]
      have h2 : θ ε * θ ε⁻¹ = 1 := by rw [mul_comm, h1]
      constructor
      · funext i
        show θ ε⁻¹ * (θ ε * y i) = y i
        rw [← mul_assoc, h1, one_mul]
      · funext i
        show θ ε * (θ ε⁻¹ * y i) = y i
        rw [← mul_assoc, h2, one_mul])
    (fun ε hε => _root_.GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi F hF θ hθ li hli.1 ι ε hε)
    (fun B hB U hU => by
      have h0 : ∀ b ∈ B, ∀ᶠ z : ℝ × (ι → Ainf F) in 𝓝 ((0 : ℝ), b), T z.1 z.2 ∈ U := by
        intro b _
        refine hjoint.continuousAt.eventually_mem ?_
        have : T (0 : ℝ) b = 0 := by
          funext i
          show θ 0 * b i = 0
          rw [hθ0, zero_mul]
        simpa [this] using hU
      exact (hB.eventually_forall_of_forall_eventually h0).filter_mono nhdsWithin_le_nhds)
    (fun i => algebraMap F (Ainf F) (x0 i)) φ hφ hφs
  rw [hcard] at key

  let f : latCoset I x0 → Λ := fun x => ⟨fun i => algebraMap F (Ainf F) (x.1 i - x0 i), fun i _ => by
    obtain ⟨y, hy, e⟩ := x.2 i
    refine AddSubgroup.mem_map.2 ⟨y, hy, ?_⟩
    show algebraMap F (Ainf F) (y : F) = algebraMap F (Ainf F) (x.1 i - x0 i)
    rw [e]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x x' h
      refine Subtype.ext (funext fun i => ?_)
      have h1 := hg (congrFun (congrArg Subtype.val h) i)
      exact sub_left_injective h1
    · rintro ⟨l, hl⟩
      have hy : ∀ i, ∃ y ∈ I, j y = l i := fun i => by
        obtain ⟨y, hy, e⟩ := AddSubgroup.mem_map.1 (hl i (Set.mem_univ i))
        exact ⟨y, hy, e⟩
      choose y hyI hyl using hy
      refine ⟨⟨fun i => x0 i + (y i : F), fun i => ⟨y i, hyI i, by simp⟩⟩, Subtype.ext (funext fun i => ?_)⟩
      show algebraMap F (Ainf F) (x0 i + (y i : F) - x0 i) = l i
      rw [add_sub_cancel_left, ← hyl]
      rfl
  let e : latCoset I x0 ≃ Λ := Equiv.ofBijective f hf
  have hterm : ∀ (ε : ℝ) (x : latCoset I x0), φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i)) =
      φ (T ε ((fun i => algebraMap F (Ainf F) (x0 i)) + (e x : ι → Ainf F))) := by
    intro ε x
    congr 1
    funext i
    show _ = θ ε * (algebraMap F (Ainf F) (x0 i) + algebraMap F (Ainf F) (x.1 i - x0 i))
    rw [← map_add (f := _), add_sub_cancel]
  constructor
  · intro ε hε
    have h1 := (e.summable_iff (f := fun l : Λ => φ (T ε ((fun i => algebraMap F (Ainf F) (x0 i)) + l)))).2 (key.1 ε hε)
    refine h1.congr fun x => ?_
    exact (hterm ε x).symm
  · refine key.2.congr fun ε => ?_
    congr 1
    rw [← e.tsum_eq]
    exact tsum_congr fun x => (hterm ε x).symm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterTrivialFiniteCovolume
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SW.CharacterTrivial

theorem eq_one_of_isFundamentalDomain :
    ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
      [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
      (Γ₁ : Subgroup G₁) [Countable Γ₁] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁),
      IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → ∀ δ : G₁ →* ℝ≥0, Measurable δ →
        (∀ γ ∈ Γ₁, δ γ = 1) → ∀ u, δ u = 1 := by
  intro G₁ _ _ _ _ _ _ _ _ Γ₁ _ μ₁ _ 𝓕₁ h𝓕₁ hfin δ hδ hγ
  obtain ⟨h0, hR, -⟩ :=
    GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain G₁ Γ₁ μ₁ 𝓕₁ h𝓕₁ hfin
  have hinv : ∀ u, δ u * δ u⁻¹ = 1 := fun u => by rw [← map_mul, mul_inv_cancel, map_one]
  have hpos : ∀ u, 0 < (δ u : ℝ) := by
    intro u
    have h : δ u ≠ 0 := left_ne_zero_of_mul_eq_one (hinv u)
    exact_mod_cast pos_iff_ne_zero.2 h
  have hδr : Measurable (fun u => (δ u : ℝ)) := measurable_coe_nnreal_real.comp hδ
  have hind : ∀ (A B : Set G₁) (x y : G₁), (x ∈ A ↔ y ∈ B) →
      A.indicator (1 : G₁ → ℝ≥0∞) x = B.indicator (1 : G₁ → ℝ≥0∞) y := by
    intro A B x y h
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (h.1 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun hy => hx (h.2 hy))]
  have hbig : ∀ u₀, 1 < δ u₀ → False := by
    intro u₀ ht
    obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = δ u₀ := ⟨_, rfl⟩
    have ht1 : 1 < t := by rw [htdef]; exact_mod_cast ht
    have ht0 : 0 < t := by linarith
    let C : ℤ → Set G₁ := fun n => (fun u => (δ u : ℝ)) ⁻¹' Set.Ico (t ^ n) (t ^ (n + 1))
    have hCm : ∀ n, MeasurableSet (C n) := fun n => hδr measurableSet_Ico
    have hmem : ∀ n u, u * u₀ ∈ C (n + 1) ↔ u ∈ C n := by
      intro n u
      have e : (δ (u * u₀) : ℝ) = δ u * t := by rw [map_mul, htdef]; push_cast; rfl
      simp only [C, Set.mem_preimage, Set.mem_Ico, e]
      rw [zpow_add_one₀ ht0.ne' n, zpow_add_one₀ ht0.ne' (n + 1),
        mul_le_mul_iff_of_pos_right ht0, mul_lt_mul_iff_of_pos_right ht0, zpow_add_one₀ ht0.ne' n]
    have hshift : ∀ n, (μ₁.restrict 𝓕₁) (C n) = (μ₁.restrict 𝓕₁) (C (n + 1)) := by
      intro n
      have hinvar : ∀ γ ∈ Γ₁, ∀ u, (C (n + 1)).indicator (1 : G₁ → ℝ≥0∞) (γ * u) =
          (C (n + 1)).indicator (1 : G₁ → ℝ≥0∞) u := by
        intro γ hg u
        have e : γ * u ∈ C (n + 1) ↔ u ∈ C (n + 1) := by
          simp only [C, Set.mem_preimage, map_mul, hγ γ hg, one_mul]
        exact hind _ _ _ _ e
      have e := GlobalTheory.CompanionTheory.SW.Averaging.setLIntegral_mul_right_eq μ₁ Γ₁ 𝓕₁ h𝓕₁
        ((C (n + 1)).indicator 1) hinvar u₀
      have e' : (fun u => (C (n + 1)).indicator (1 : G₁ → ℝ≥0∞) (u * u₀)) =
          (C n).indicator 1 := by
        funext u
        exact hind _ _ _ _ (hmem n u)
      rw [e', lintegral_indicator_one (hCm n), lintegral_indicator_one (hCm (n + 1))] at e
      exact e
    have hconst : ∀ n, (μ₁.restrict 𝓕₁) (C n) = (μ₁.restrict 𝓕₁) (C 0) := by
      intro n
      induction n using Int.induction_on with
      | zero => rfl
      | succ i ih => rw [← hshift]; exact ih
      | pred i ih =>
        rw [← ih, hshift (-(i : ℤ) - 1)]
        congr 2
        ring
    have hU : ⋃ n, C n = Set.univ := by
      refine Set.eq_univ_of_forall fun u => Set.mem_iUnion.2 ?_
      obtain ⟨n, hn⟩ := exists_mem_Ico_zpow (hpos u) ht1
      exact ⟨n, hn⟩
    have hdisj : Pairwise (Function.onFun Disjoint C) := by
      intro m n hmn
      refine Set.disjoint_left.2 fun u h₁ h₂ => hmn ?_
      have a : t ^ n < t ^ (m + 1) := lt_of_le_of_lt h₂.1 h₁.2
      have b : t ^ m < t ^ (n + 1) := lt_of_le_of_lt h₁.1 h₂.2
      have a' := (zpow_lt_zpow_iff_right₀ ht1).1 a
      have b' := (zpow_lt_zpow_iff_right₀ ht1).1 b
      omega
    have hsum : μ₁ 𝓕₁ = ∑' _ : ℤ, (μ₁.restrict 𝓕₁) (C 0) := by
      rw [← Measure.restrict_apply_univ 𝓕₁, ← hU, measure_iUnion hdisj hCm]
      exact tsum_congr hconst
    by_cases hz : (μ₁.restrict 𝓕₁) (C 0) = 0
    · rw [hz, tsum_zero] at hsum
      exact h0 hsum
    · rw [ENNReal.tsum_const_eq_top_of_ne_zero hz] at hsum
      exact hfin.ne hsum
  intro u
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine hbig u⁻¹ ?_
    by_contra hle
    have h1 : δ u * δ u⁻¹ < 1 * 1 :=
      mul_lt_mul'' hlt (lt_of_le_of_ne (not_lt.1 hle) ?_) zero_le zero_le
    · rw [hinv u, one_mul] at h1
      exact lt_irrefl _ h1
    · intro e
      have := hinv u
      rw [e, mul_one] at this
      exact hne this
  · exact hbig u hgt

end GlobalTheory.CompanionTheory.SW.CharacterTrivial
end

