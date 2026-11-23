module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0007
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0005
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0003
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.LiftIntegral
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitOnSpec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AveragingTransferKills
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

variable {l : ℕ} [Fact l.Prime]

private abbrev coefT (l : ℕ) [Fact l.Prime] (n : ℕ) : Test l ⥤ ModuleCat.{0} (Acris l) :=
  CH.modF (testι l ⋙ AcrA l n)

private lemma add_gen {C : Type 1} [Category.{0} C] (Pa : Parts C) {R : Type} [CommRing R]
    (F : C ⥤ ModuleCat.{0} R)
    (hF : ∀ (A : C) (S : Fam A), Pa.Cov S →
      Function.Bijective fun (x : F.obj A) (i : S.ι) => (F.map (S.f i)).hom x)
    (F' : Coef C) (c : ∀ A, F.obj A ≃+ F'.obj A)
    (hc : ∀ {A B : C} (φ : A ⟶ B) (x : F.obj A), c B ((F.map φ).hom x) = (F'.map φ).hom (c A x)) :
    Pa.Add F' := by
  intro A S hS
  have e : (fun (x : F'.obj A) (i : S.ι) => (F'.map (S.f i)).hom x) =
      (fun (v : ∀ i, F.obj (S.B i)) (i : S.ι) => c (S.B i) (v i)) ∘
        (fun (x : F.obj A) (i : S.ι) => (F.map (S.f i)).hom x) ∘ (c A).symm := by
    funext x i
    have := hc (S.f i) ((c A).symm x)
    rw [AddEquiv.apply_symm_apply] at this
    exact this.symm
  rw [e]
  exact (Equiv.piCongrRight fun i => (c (S.B i)).toEquiv).bijective.comp
    ((hF A S hS).comp (c A).symm.bijective)

private lemma coefT_add (hA : AcrAdd) (Pa : Parts (Test l))
    (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S) (n : ℕ) (A : Test l) (S : Fam A)
    (hS : Pa.Cov S) :
    Function.Bijective fun (x : (coefT l n).obj A) (i : S.ι) => ((coefT l n).map (S.f i)).hom x :=
  hA l n A S ((hPa A S).1 hS)

private lemma avg_gen (hLA : LocAvg) {C : Type 1} [Category.{0} C] (Pa : Parts C) (T : Theory C)
    {R : Type} [CommRing R] (F : C ⥤ ModuleCat.{0} R) (F' : Coef C) (hF : Pa.Add F')
    (e : ∀ (P : C ⥤ Type) (j : ℕ), CH.H (CategoryOfElements.π P ⋙ F) j ≃+ T.H P F' j)
    {Q P : C ⥤ Type} (p : Q ⟶ P) {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (hL : Pa.LocTrans p g)
    (m : CH.Mor (CategoryOfElements.π P ⋙ F) (CategoryOfElements.π Q ⋙ F) (RingHom.id R)) (j : ℕ)
    (hm : ∀ x, e Q j (m.pull j x) = T.pull p F' j (e P j x))
    (x : CH.H (CategoryOfElements.π P ⋙ F) j) (hx : m.pull j x = 0) : Fintype.card I • x = 0 := by
  have h0 : T.pull p F' j (e P j x) = 0 := by
    simpa only [hx, AddEquiv.map_zero] using (hm x).symm
  apply (e P j).injective
  change (e P j).toAddMonoidHom (Fintype.card I • x) = (e P j).toAddMonoidHom 0
  rw [map_nsmul, map_zero]
  exact hLA C Pa T F' hF Q P p I g hL j _ h0

private def pullT {Q P : PAlg l ⥤ Type} (p : Q ⟶ P) (n : ℕ) :
    CH.Mor (CategoryOfElements.π (testι l ⋙ P) ⋙ coefT l n)
      (CategoryOfElements.π (testι l ⋙ Q) ⋙ coefT l n) (RingHom.id _) := pullMor p n

private lemma locTrans_of {Q P : PAlg l ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I]
    {g : I → (Q ⟶ Q)} (h : TTrans p g) (Pa : Parts (Test l))
    (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S) :
    Pa.LocTrans (Functor.whiskerLeft (testι l) p)
      (fun i => Functor.whiskerLeft (testι l) (g i)) := by
  refine ⟨fun i => ?_, fun A => h.2.1 A, fun A y y' hy => ?_⟩
  · rw [← Functor.whiskerLeft_comp, h.1 i]
  · obtain ⟨S, hS, hm⟩ := h.2.2 A y y' hy
    exact ⟨S, (hPa A S).2 hS, hm⟩

private lemma averaging_transfer_kills (hLA : LocAvg) (hP : PartsEx) (hA : AcrAdd) (hT : TheoryEx)
    {Q P : PAlg l ⥤ Type} (p : Q ⟶ P) {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : TTrans p g)
    (n j : ℕ) (x : CH.H (CategoryOfElements.π (testι l ⋙ P) ⋙ coefT l n) j)
    (hx : (pullT p n).pull j x = 0) : Fintype.card I • x = 0 := by
  refine Exists.elim (hP l) fun Pa hPa => Exists.elim (hT (Test l)) fun T hT => ?_
  refine Exists.elim (hT (Acris l) (coefT l n)) fun F' h1 => Exists.elim h1 fun c h2 =>
    Exists.elim h2 fun e h3 => ?_
  have hF : Pa.Add F' := add_gen Pa (coefT l n) (coefT_add hA Pa hPa n) F' c h3.1
  have hG : (pullT p n).G = CategoryOfElements.map (Functor.whiskerLeft (testι l) p) := rfl
  have hτ : ∀ (T : (testι l ⋙ Q).Elements) (y : ((CategoryOfElements.π (testι l ⋙ P) ⋙ coefT l n).obj ((pullT p n).G.obj T))),
      HEq ((pullT p n).τ T y) y := fun _ _ => HEq.rfl
  have hm := h3.2 (Functor.whiskerLeft (testι l) p) (pullT p n) hG hτ j
  have hL := locTrans_of h Pa hPa
  exact avg_gen hLA Pa T (coefT l n) F' hF e (Functor.whiskerLeft (testι l) p) hL (pullT p n) j hm x hx

end UpperTheory.Ru.crystallineComparison

open CategoryTheory CategoryTheory.Limits GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.avgMH :
    UpperTheory.Ru.crystallineComparison.AvgMH := by
  intro l _ Q P p I _ g h n j x hx
  exact averaging_transfer_kills locAvg partsEx acrAdd theoryEx p h n j x hx
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitPointGeneric
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

section Act

variable {l : ℕ} {Y : Scheme.{0}} {J : Type} {T : J → Corr l Y} (D : WDat l T)

private lemma unit_away (U : Type) [CommRing U] :
    IsUnit ((l : ℕ) : Γ(Spec (CommRingCat.of (Localization.Away (l : U))), ⊤)) := by
  have hunit : IsUnit ((l : ℕ) : Localization.Away (l : U)) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : U)) (l : U)
    simpa using this
  have := hunit.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (l : U)))).inv.hom
  rwa [map_natCast] at this

private lemma split_point_generic {U : Type} [CommRing U] (w : Spec (CommRingCat.of U) ⟶ D.W) (j : J) :
    SplitOn (T j).p (awayPt l U ≫ w ≫ D.π) fun i => awayPt l U ≫ w ≫ D.s j i := by
  have h := D.gen _ (awayPt l U ≫ w) (unit_away U) j
  simp only [Category.assoc] at h
  exact h

private lemma split_pt {U : Type} [CommRing U] (w : Spec (CommRingCat.of U) ⟶ D.W)
    (σ : ∀ j, Equiv.Perm (Fin (T j).d)) (j : J) :
    SplitOn (T j).p (awayPt l U ≫ w ≫ D.π) fun i => awayPt l U ≫ w ≫ D.s j (σ j i) :=
  (splitRules.1 _ _ (𝟙 _) _ (split_point_generic D w j)).2 (σ j)

private lemma act_ex {U : Type} [CommRing U] (hl : (l : U) ∈ nonZeroDivisors U)
    (w : Spec (CommRingCat.of U) ⟶ D.W) (σ : ∀ j, Equiv.Perm (Fin (T j).d)) :
    ∃! w₁ : Spec (CommRingCat.of U) ⟶ D.W, w₁ ≫ D.π = w ≫ D.π ∧ ∀ j i, w₁ ≫ D.s j i = w ≫ D.s j (σ j i) :=
  D.univ U hl (w ≫ D.π) (fun j i => w ≫ D.s j (σ j i)) (fun j i => by rw [Category.assoc, D.hs])
    (fun j => split_pt D w σ j)

private def act {U : Type} [CommRing U] (hl : (l : U) ∈ nonZeroDivisors U)
    (w : Spec (CommRingCat.of U) ⟶ D.W) (σ : ∀ j, Equiv.Perm (Fin (T j).d)) :
    Spec (CommRingCat.of U) ⟶ D.W := (act_ex D hl w σ).exists.choose

private lemma act_spec {U : Type} [CommRing U] (hl : (l : U) ∈ nonZeroDivisors U)
    (w : Spec (CommRingCat.of U) ⟶ D.W) (σ : ∀ j, Equiv.Perm (Fin (T j).d)) :
    act D hl w σ ≫ D.π = w ≫ D.π ∧ ∀ j i, act D hl w σ ≫ D.s j i = w ≫ D.s j (σ j i) :=
  (act_ex D hl w σ).exists.choose_spec

private lemma act_eq {U : Type} [CommRing U] (hl : (l : U) ∈ nonZeroDivisors U)
    (w w₁ : Spec (CommRingCat.of U) ⟶ D.W) (σ : ∀ j, Equiv.Perm (Fin (T j).d))
    (h₁ : w₁ ≫ D.π = w ≫ D.π) (h₂ : ∀ j i, w₁ ≫ D.s j i = w ≫ D.s j (σ j i)) :
    act D hl w σ = w₁ :=
  (act_ex D hl w σ).unique (act_spec D hl w σ) ⟨h₁, h₂⟩

end Act

section Idem

variable {R : Type} [CommRing R]

private lemma coi_pi {J : Type} [Fintype J] [DecidableEq J] {I : J → Type} [∀ j, Fintype (I j)]
    (e : ∀ j, I j → R) (he : ∀ j, CompleteOrthogonalIdempotents (e j)) :
    CompleteOrthogonalIdempotents fun τ : (∀ j, I j) => ∏ j, e j (τ j) := by
  refine ⟨⟨fun τ => ?_, fun τ τ' h => ?_⟩, ?_⟩
  · change (∏ j, e j (τ j)) * (∏ j, e j (τ j)) = ∏ j, e j (τ j)
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => (he j).toOrthogonalIdempotents.idem (τ j)
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
    change (∏ j, e j (τ j)) * (∏ j, e j (τ' j)) = 0
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_zero (Finset.mem_univ j) ((he j).toOrthogonalIdempotents.ortho hj)
  · have h : ∏ j, ∑ i, e j i = 1 := by simp [fun j => (he j).complete]
    rw [Finset.prod_univ_sum] at h
    simpa [Fintype.piFinset_univ] using h

end Idem

variable {l : ℕ} [Fact l.Prime]

private lemma lift_coi (A : PAlg l) {I : Type} [Fintype I] (e : I → A.U)
    (he : CompleteOrthogonalIdempotents e) :
    ∃ e₀ : I → A.A, CompleteOrthogonalIdempotents e₀ ∧ ∀ i, A.sharp (e₀ i) = e i := by
  classical
  have s1 : A.sharp 1 = 1 := map_one _
  have s0 : A.sharp 0 = 0 := by
    have := (RL.sharp_cong A).2.2 1 IsIdempotentElem.one
    simpa [s1] using this
  have hsub : ∀ a : A.A, IsIdempotentElem a → A.sharp (1 - a) = 1 - A.sharp a := (RL.sharp_cong A).2.2
  have h := fun i => (RL.idem_au A (e i) (he.toOrthogonalIdempotents.idem i)).exists
  choose e₀ h1 h2 using h
  have hz : ∀ a : A.A, IsIdempotentElem a → A.sharp a = 0 → a = 0 := fun a ha hs =>
    (RL.idem_au A 0 IsIdempotentElem.zero).unique ⟨ha, hs⟩ ⟨IsIdempotentElem.zero, s0⟩
  have ho : ∀ a : A.A, IsIdempotentElem a → A.sharp a = 1 → a = 1 := fun a ha hs =>
    (RL.idem_au A 1 IsIdempotentElem.one).unique ⟨ha, hs⟩ ⟨IsIdempotentElem.one, s1⟩
  have hort : ∀ i j, i ≠ j → e₀ i * e₀ j = 0 := fun i j hij =>
    hz _ ((h1 i).mul (h1 j)) (by
      rw [map_mul, h2, h2]
      exact he.toOrthogonalIdempotents.ortho hij)
  have hsum : ∀ s : Finset I, IsIdempotentElem (∑ i ∈ s, e₀ i) ∧ A.sharp (∑ i ∈ s, e₀ i) = ∑ i ∈ s, e i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨by simpa using IsIdempotentElem.zero, by simpa using s0⟩
    | insert a s ha ih =>
      obtain ⟨i1, i2⟩ := ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hbc : e₀ a * ∑ i ∈ s, e₀ i = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi => hort a i fun h => ha (h ▸ hi)
      have hid : IsIdempotentElem (e₀ a + ∑ i ∈ s, e₀ i) := by
        have e1 : e₀ a * e₀ a = e₀ a := h1 a
        have e2 : (∑ i ∈ s, e₀ i) * (∑ i ∈ s, e₀ i) = ∑ i ∈ s, e₀ i := i1
        change (e₀ a + ∑ i ∈ s, e₀ i) * (e₀ a + ∑ i ∈ s, e₀ i) = _
        rw [add_mul, mul_add, mul_add, e1, e2, hbc, mul_comm, hbc]
        simp
      refine ⟨hid, ?_⟩
      have hx : e₀ a + ∑ i ∈ s, e₀ i = 1 - (1 - e₀ a) * (1 - ∑ i ∈ s, e₀ i) := by
        linear_combination hbc
      have hm : A.sharp (e₀ a) * A.sharp (∑ i ∈ s, e₀ i) = 0 := by
        rw [← map_mul, hbc, s0]
      rw [hx, hsub _ ((h1 a).one_sub.mul i1.one_sub), map_mul, hsub _ (h1 a), hsub _ i1, h2, ← i2]
      rw [h2] at hm
      linear_combination -hm
  refine ⟨e₀, ⟨⟨h1, fun i j hij => hort i j hij⟩, ?_⟩, h2⟩
  obtain ⟨i1, i2⟩ := hsum Finset.univ
  exact ho _ i1 (by rw [i2, he.complete])

variable {O : Type} [CommRing O] {Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of O)} {J : Type}
  {T : J → Corr l Y}

private def gAct (κ : O →+* OC l) (D : WDat l T) (σ : ∀ j, Equiv.Perm (Fin (T j).d)) :
    PX (D.π ≫ q) κ ⟶ PX (D.π ≫ q) κ where
  app A := TypeCat.ofHom fun w => ⟨act D (RL.u_tf A).1 w.1 σ, by
    rw [← Category.assoc, (act_spec D (RL.u_tf A).1 w.1 σ).1, Category.assoc]
    exact w.2⟩
  naturality A B f := by
    ext w
    refine Subtype.ext ?_
    change act D (RL.u_tf B).1 (Spec.map (CommRingCat.ofHom (PAlg.mapU f)) ≫ w.1) σ =
      Spec.map (CommRingCat.ofHom (PAlg.mapU f)) ≫ act D (RL.u_tf A).1 w.1 σ
    refine act_eq D _ _ _ σ ?_ fun j i => ?_
    · rw [Category.assoc, (act_spec D (RL.u_tf A).1 w.1 σ).1, Category.assoc]
    · rw [Category.assoc, (act_spec D (RL.u_tf A).1 w.1 σ).2, Category.assoc]

end UpperTheory.Ru.crystallineComparison

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.wTrans :
    UpperTheory.Ru.crystallineComparison.WTrans := by
  intro l _ O _ Y q κ J _ _ T D
  refine ⟨fun σ => gAct κ D σ, ?_, ?_, ?_⟩
  · intro σ
    ext A w
    refine Subtype.ext ?_
    exact (act_spec D (RL.u_tf A).1 w.1 σ).1
  · intro A y
    have hT := testFacts l A.obj A.property
    have hz : ∀ j, ∃ z : Fin (T j).d → (Spec (CommRingCat.of A.obj.U) ⟶ (T j).Z), (∀ i, z i ≫ (T j).p = y.1) ∧
        SplitOn (T j).p (awayPt l A.obj.U ≫ y.1) fun i => awayPt l A.obj.U ≫ z i := fun j =>
      splitEx l Fact.out Y (T j) A.obj.U hT.1 hT.2.1 hT.2.2.1 y.1
    choose z hz hs using hz
    obtain ⟨w, ⟨hw, -⟩, -⟩ := D.univ A.obj.U hT.1 y.1 z hz hs
    exact ⟨⟨w, by rw [← Category.assoc, hw]; exact y.2⟩, Subtype.ext hw⟩
  · intro A w w' hp
    have hT := testFacts l A.obj A.property
    have hww : w.1 ≫ D.π = w'.1 ≫ D.π := congrArg Subtype.val hp
    have hperm : ∀ j, ∃ e : Equiv.Perm (Fin (T j).d) → A.obj.U, CompleteOrthogonalIdempotents e ∧
        ∀ (σ : Equiv.Perm (Fin (T j).d)) (V : Type) [CommRing V] (ρ : A.obj.U →+* V), ρ (e σ) = 1 → ∀ i,
          Spec.map (CommRingCat.ofHom ρ) ≫ w'.1 ≫ D.s j i = Spec.map (CommRingCat.ofHom ρ) ≫ w.1 ≫ D.s j (σ i) := fun j =>
      splitPerm l Y (T j) A.obj.U hT.1 hT.2.1 (w.1 ≫ D.π) (fun i => w.1 ≫ D.s j i) (fun i => w'.1 ≫ D.s j i)
        (fun i => by rw [Category.assoc, D.hs]) (fun i => by rw [Category.assoc, D.hs, hww])
        (split_point_generic D w.1 j) (by rw [hww]; exact split_point_generic D w'.1 j)
    choose e he hE using hperm
    obtain ⟨e₀, he₀, hs⟩ := lift_coi A.obj _ (coi_pi e he)
    obtain ⟨B, f, hdec, hf⟩ := decEx l A (∀ j, Equiv.Perm (Fin (T j).d)) e₀ he₀
    refine ⟨(⟨_, B, f⟩ : Fam A), hdec, fun τ => ?_⟩
    let ρ : A.obj.U →+* (B τ).obj.U := PAlg.mapU (f τ).hom
    have hρ : ρ (∏ j, e j (τ j)) = 1 := by
      rw [← hs τ]
      refine ((RL.expand_nat A.obj (B τ).obj (f τ).hom).2.2.1 (e₀ τ)).trans ?_
      rw [hf τ, map_one]
    have hρj : ∀ j, ρ (e j (τ j)) = 1 := by
      intro j
      have h1 := hρ
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), map_mul] at h1
      have h2 : ρ (e j (τ j)) * ρ (e j (τ j)) = ρ (e j (τ j)) := by
        rw [← map_mul, (he j).toOrthogonalIdempotents.idem (τ j)]
      calc ρ (e j (τ j)) = ρ (e j (τ j)) * (ρ (e j (τ j)) * _) := by rw [h1, mul_one]
        _ = _ := by rw [← mul_assoc, h2, h1]
    have key : ∀ j i, Spec.map (CommRingCat.ofHom ρ) ≫ w'.1 ≫ D.s j i =
        Spec.map (CommRingCat.ofHom ρ) ≫ w.1 ≫ D.s j (τ j i) := fun j i => hE j (τ j) _ ρ (hρj j) i
    have hstep : ∀ σ, (gAct κ D σ).app _ ((PX (D.π ≫ q) κ).map (f τ).hom w') =
        (gAct κ D (τ * σ)).app _ ((PX (D.π ≫ q) κ).map (f τ).hom w) := by
      intro σ
      refine Subtype.ext ?_
      change act D (RL.u_tf _).1 (Spec.map (CommRingCat.ofHom ρ) ≫ w'.1) σ =
        act D (RL.u_tf _).1 (Spec.map (CommRingCat.ofHom ρ) ≫ w.1) (τ * σ)
      refine act_eq D _ _ _ σ ?_ fun j i => ?_
      · rw [(act_spec D _ _ _).1, Category.assoc, Category.assoc, hww]
      · rw [(act_spec D _ _ _).2]
        simp only [Category.assoc]
        rw [key]
        rfl
    simp only [hstep]
    have hm := Multiset.map_univ_val_equiv (Equiv.mulLeft τ)
    conv_lhs => rw [← hm]
    rw [Multiset.map_map]
    rfl
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SumTransportAlt
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

private theorem bij_transport {ι X X' : Type*} {Y Y' : ι → Type*} (c : X ≃ X') (d : ∀ i, Y i ≃ Y' i)
    (g : ∀ i, X → Y i) (f : ∀ i, X' → Y' i) (h : ∀ i x, f i (c x) = d i (g i x))
    (hb : Function.Bijective fun x i => g i x) : Function.Bijective fun x i => f i x := by
  obtain ⟨hi, hs⟩ := hb
  refine ⟨fun x y hxy => ?_, fun b => ?_⟩
  · obtain ⟨x, rfl⟩ := c.surjective x
    obtain ⟨y, rfl⟩ := c.surjective y
    refine congrArg c (hi (funext fun i => (d i).injective ?_))
    have := congrFun hxy i
    simpa only [h] using this
  · obtain ⟨x, hx⟩ := hs fun i => (d i).symm (b i)
    refine ⟨c x, funext fun i => ?_⟩
    have := congrFun hx i
    simp only at this
    simp only [h, this, Equiv.apply_symm_apply]

private theorem sum_transport {W Y I : Type*} [AddCommGroup W] [AddCommGroup Y] [Fintype I] (a : I → ℤ) (e : Y ≃+ W)
    (f : I → Y) (g : I → W) (h : ∀ i, e (f i) = g i) (key : ∑ i, a i • g i = 0) : ∑ i, a i • f i = 0 := by
  apply e.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum]
  simp only [map_zsmul, h]
  exact key

variable {l : ℕ} [Fact l.Prime]

private theorem empty_isDec {A : Test l} (h : Subsingleton A.obj.A) :
    IsDec (⟨Empty, fun e => e.elim, fun e => e.elim⟩ : Fam A) := by
  refine ⟨fun x y _ => Subsingleton.elim x y, fun b => ⟨0, ?_⟩⟩
  funext e
  exact e.elim

private theorem locZero_of {Pa : Parts (Test l)} (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S)
    {Q P : PAlg l ⥤ Type} {I : Type} [Fintype I] {a : I → ℤ} {u : I → (Q ⟶ P)} (hz : TZero a u) :
    Pa.LocZero (Q := testι l ⋙ Q) (P := testι l ⋙ P) a (fun i => Functor.whiskerLeft (testι l) (u i)) := by
  intro A y
  obtain ⟨S, hS, hs⟩ := hz A y
  refine ⟨S, (hPa A S).2 hS, fun s => ?_⟩
  rcases hs s with h0 | h0
  · exact Or.inl h0
  · exact Or.inr ((hPa _ _).2 (empty_isDec h0))

private theorem add_of {Pa : Parts (Test l)} (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S)
    (n : ℕ) (hacr : AcrAdd) (F' : Coef (Test l)) (c : ∀ A, (testι l ⋙ AcrF l n).obj A ≃+ F'.obj A)
    (hc : ∀ {A B : Test l} (φ : A ⟶ B) (x : (testι l ⋙ AcrF l n).obj A),
      c B (((testι l ⋙ AcrF l n).map φ).hom x) = (F'.map φ).hom (c A x)) : Pa.Add F' := by
  intro A S hS
  exact bij_transport (c A).toEquiv (fun i => (c (S.B i)).toEquiv) (fun i x => PAlg.mapAcr (S.f i).hom n x)
    (fun i x => (F'.map (S.f i)).hom x) (fun i x => (hc (S.f i) x).symm) (hacr l n A S ((hPa A S).1 hS))

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.sumMH :
    UpperTheory.Ru.crystallineComparison.SumMH := by
  intro l _ Q P I _ a u hz n j x
  refine (partsEx l).elim fun Pa hPa => (theoryEx (Test l)).elim fun T hT => ?_
  refine (hT (Acris l) (testι l ⋙ AcrF l n)).elim fun F' h1 => h1.elim fun c h2 => h2.elim fun e h3 => ?_
  have hAdd : Pa.Add F' := add_of hPa n acrAdd F' c h3.1
  have key := locSum (Test l) Pa T F' hAdd (testι l ⋙ Q) (testι l ⋙ P) I a
    (fun i => Functor.whiskerLeft (testι l) (u i)) (locZero_of hPa hz) j
  have hp : ∀ i, e (testι l ⋙ Q) j (pullH (u i) n j x) =
      T.pull (Functor.whiskerLeft (testι l) (u i)) F' j (e (testι l ⋙ P) j x) := fun i =>
    h3.2 (Functor.whiskerLeft (testι l) (u i)) (pullMor (u i) n) rfl (fun _ _ => HEq.rfl) j x
  exact sum_transport a (e (testι l ⋙ Q) j) _ _ hp (key (e (testι l ⋙ P) j x))
end
end

