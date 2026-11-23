module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0040
public import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.KillCokOf
public import Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration.CechLevelIso
public import Development.EtaleCohomology.EtaleSheaves.CechLevelIsomorphism.BaseChangeLimit
public import Development.EtaleCohomology.EtaleSheaves.Bundle0065
public import Development.EtaleCohomology.EtaleSheaves.ZeroSheafMaps.EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerat

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.BijOfIso
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut LateralTheory.E.KillCokPf.Asm

namespace LateralTheory.E.KernelLocalization

theorem bij_of_iso (R : Type) [CommRing R] (F : Shv R) {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (n : ℤ) :
    Function.Bijective (pull R (sch.map f) F n) := by
  have h1 : ∀ x, pull R (sch.map (inv f)) F n (pull R (sch.map f) F n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  have h2 : ∀ x, pull R (sch.map f) F n (pull R (sch.map (inv f)) F n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem cover_bij (hC : Coprod) (R : Type) [CommRing R] (F : Shv R) {ι : Type} {X : ι → Scheme.{0}} {S : Scheme.{0}}
    (π : ∀ j, X j ⟶ S) [IsIso (Sigma.desc π)] (n : ℤ) :
    Function.Bijective fun (x : H R (sch.obj S) F n) (j : ι) => pull R (sch.map (π j)) F n x := by
  have := (hC R F X n).comp (bij_of_iso R F (Sigma.desc π) n)
  convert this using 1
  funext x j
  simp only [Function.comp]
  rw [← pull_comp, ← Functor.map_comp, Sigma.ι_desc]

abbrev pr {ι : Type} (E : ι → CommRingCat.{0}) (j : ι) : CommRingCat.of (∀ k, E k) ⟶ E j :=
  CommRingCat.ofHom (Pi.evalRingHom (fun k => E k) j)

theorem pi_bij (hC : Coprod) (q : ℕ) (i n : ℤ) {ι : Type} [Finite ι] (E : ι → CommRingCat.{0}) :
    Function.Bijective fun x (j : ι) => PP q i n (pr E j) x := by
  have : IsIso (Sigma.desc fun j => Spec.map (pr E j)) := inferInstanceAs (IsIso (sigmaSpec E))
  exact cover_bij hC _ _ _ n

theorem push_inj (hC : Coprod) (q : ℕ) (i n : ℤ) {ι : Type} [Finite ι] (E : ι → CommRingCat.{0}) {Z : CommRingCat.{0}}
    (ψ : CommRingCat.of (∀ k, E k) ⟶ Z) (y : H (ZMod q) (sch.obj (Spec Z)) (tw q i) n)
    (hy : ∀ j, PP q i n (pushout.inl ψ (pr E j)) y = 0) : y = 0 := by
  have h0 : IsIso (Sigma.desc fun j => Spec.map (pr E j)) := inferInstanceAs (IsIso (sigmaSpec E))
  have := FinitaryPreExtensive.isIso_sigmaDesc_fst (fun j => Spec.map (pr E j)) (Spec.map ψ) h0
  apply (cover_bij hC (ZMod q) (tw q i) (fun j => pullback.fst (Spec.map ψ) (Spec.map (pr E j))) n).1
  funext j
  have hp := isPullback_SpecMap_of_isPushout _ _ _ _ (IsPushout.of_hasPushout ψ (pr E j))
  simp only [map_zero]
  rw [← hp.isoPullback_inv_fst, Functor.map_comp, pull_comp]
  change pull _ _ _ _ (PP q i n _ y) = 0
  rw [hy, map_zero]

theorem rel_pi (hC : Coprod) (q : ℕ) (i n : ℤ) {D Y : CommRingCat.{0}} (φ : D ⟶ Y) {ι : Type} [Finite ι]
    (E : ι → CommRingCat.{0}) (e : ∀ j, D ⟶ E j) (z : HR q i n φ)
    (hz : ∀ j, ∃ (Z : CommRingCat.{0}) (u : Y ⟶ Z) (ψ : E j ⟶ Z) (h : IsPushout φ (e j) u ψ), RP q i n φ (e j) u ψ h.w z = 0)
    {Z : CommRingCat.{0}} (u : Y ⟶ Z) (ψ : CommRingCat.of (∀ k, E k) ⟶ Z) (h : IsPushout φ (piMap E e) u ψ) :
    RP q i n φ (piMap E e) u ψ h.w z = 0 := by
  have hpr : ∀ j, piMap E e ≫ pr E j = e j := fun j => by ext a; rfl
  have hw : ∀ j, φ ≫ u ≫ pushout.inl ψ (pr E j) = e j ≫ pushout.inr ψ (pr E j) := fun j => by
    rw [h.w_assoc, pushout.condition, ← Category.assoc, hpr]
  have hj : ∀ j, RP q i n ψ (pr E j) (pushout.inl ψ (pr E j)) (pushout.inr ψ (pr E j)) pushout.condition
      (RP q i n φ (piMap E e) u ψ h.w z) = 0 := fun j => by
    obtain ⟨Z', u', ψ', h', h0⟩ := hz j
    rw [← RP_comp q i n φ _ u ψ h.w _ _ _ _ (e j) _ (hw j) (hpr j) rfl,
      RP_comp q i n φ (e j) u' ψ' h'.w (𝟙 _) (h'.desc _ _ (hw j)) _ (by simp) (e j) _ (hw j) (by simp) (by simp),
      h0, map_zero]
  set z' := RP q i n φ (piMap E e) u ψ h.w z
  have hm : 1 + (n - 1) = n := by omega
  have hf : fgt _ _ _ n z' = 0 := by
    apply (pi_bij hC q i n E).1
    funext j
    simp only [map_zero]
    rw [← fgt_RP q i n ψ (pr E j) _ _ pushout.condition, hj, map_zero]
  obtain ⟨y, hy⟩ := exists_bd _ _ _ (n - 1) n hm z' hf
  have hb : ∀ j, ∃ w, PP q i (n - 1) (pushout.inr ψ (pr E j)) w = PP q i (n - 1) (pushout.inl ψ (pr E j)) y := fun j => by
    refine range_of_bd _ _ _ (n - 1) n hm _ ?_
    rw [← RP_bd q i (n - 1) n hm ψ (pr E j) _ _ pushout.condition, hy, hj]
  choose w hw' using hb
  obtain ⟨a, ha⟩ := (pi_bij hC q i (n - 1) E).2 w
  have hya : y - PP q i (n - 1) ψ a = 0 := push_inj hC q i (n - 1) E ψ _ fun j => by
    rw [map_sub, ← PP_comp, pushout.condition, PP_comp, ← hw' j, ← congrFun ha j, sub_self]
  rw [← hy, sub_eq_zero.1 hya]
  exact bd_pull ..

theorem relKill (hB1 : B1) (hC : Coprod) (q : ℕ) (i n : ℤ) {A Y D Y' : CommRingCat.{0}} (φ : A ⟶ Y) (hq : IsUnit (q : A))
    (d : A ⟶ D) (hpts : LocPts q i φ d) (w : Y ⟶ Y') (φ' : D ⟶ Y') (hpo : IsPushout φ d w φ') (z : HR q i n φ')
    (hz : PP q i n φ' (fgt _ _ _ n z) = 0) :
    ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (Z : CommRingCat.{0}) (u : Y' ⟶ Z) (ψ : E ⟶ Z) (h : IsPushout φ' e u ψ),
      Et e ∧ SpS e ∧ RP q i n φ' e u ψ h.w z = 0 := by
  have h' : ∀ x : PrimeSpectrum D, ∃ (E : CommRingCat.{0}) (e : D ⟶ E), Et e ∧
      x ∈ Set.range (PrimeSpectrum.comap e.hom) ∧
      ∃ (Z : CommRingCat.{0}) (u : Y' ⟶ Z) (ψ : E ⟶ Z) (h : IsPushout φ' e u ψ), RP q i n φ' e u ψ h.w z = 0 := by
    intro x
    obtain ⟨O, o, Q, hIE, hQ, hQr, hBC⟩ := hpts x.asIdeal x.isPrime
    obtain ⟨E, e, s, Z, u, ψ, h, he, hes, h0⟩ := relAt hB1 q i n φ' (unit_of d hq) o hIE
      (fun Z u ψ h => hBC Z (w ≫ u) ψ (hpo.paste_vert h)) z hz
    refine ⟨E, e, he, ⟨⟨Q.comap s.hom, inferInstance⟩, PrimeSpectrum.ext ?_⟩, Z, u, ψ, h, h0⟩
    change (Q.comap s.hom).comap e.hom = _
    rw [Ideal.comap_comap, ← CommRingCat.hom_comp, hes, hQr]
  choose E e he hx hY using h'
  obtain ⟨s, hs⟩ := LateralTheory.E.KillCokPf.Lem.finite_subcover E e he hx
  refine ⟨_, piMap (fun k : s => E k.1) (fun k => e k.1), _, _, _, IsPushout.of_hasPushout _ _,
    LateralTheory.E.KillCokPf.Glue.et_pi _ _ (fun k => he k.1), sps_pi _ _ fun x => ?_,
    rel_pi hC q i n φ' _ _ z (fun k => hY k.1) _ _ (IsPushout.of_hasPushout _ _)⟩
  obtain ⟨r, hr, hxr⟩ := hs x
  exact ⟨⟨r, hr⟩, hxr⟩

end LateralTheory.E.KernelLocalization
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CechLevelIsomorphism
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.TruncCokPf LateralTheory.E.LevelsPf.Tp Opposite LateralTheory.E.CechLevelIsoPf.Gen

namespace LateralTheory.E.CechLevelIsoPf

abbrev y {A B : CommRingCat.{0}} (f : A ⟶ B) := yoneda.map (Spec.map f)

lemma y_comp {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) : y (f ≫ g) = y g ≫ y f := by
  simp [y]

lemma ypb {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ P} {inr : C ⟶ P}
    (h : IsPushout f g inl inr) : IsPullback (y inl) (y inr) (y f) (y g) :=
  (isPullback_SpecMap_of_isPushout f g inl inr h).map yoneda

lemma mk_congr {C : Type*} [Category C] {ι : Type*} {S X W : C} {f : X ⟶ S} {b b' : W ⟶ S}
    {π π' : ι → (W ⟶ X)} (hb : b = b') (hπ : π = π') (h : ∀ i, π i ≫ f = b) (h' : ∀ i, π' i ≫ f = b') :
    WidePullbackCone.mk (f := fun _ : ι => f) b π h = WidePullbackCone.mk (f := fun _ : ι => f) b' π' h' := by
  subst hb; subst hπ; rfl

def lim0 {C : Type*} [Category C] {S X : C} (f : X ⟶ S) :
    IsLimit (WidePullbackCone.mk (f := fun _ : Fin 1 => f) f (fun _ => 𝟙 X) (fun _ => Category.id_comp f)) := by
  refine WidePullbackCone.IsLimit.mk _ (fun t => t.π 0) ?_ ?_ ?_
  · intro t
    have : t.π 0 ≫ f = t.base := WidePullbackCone.condition t 0
    exact this
  · intro t i
    have : t.π 0 ≫ 𝟙 X = t.π i := by rw [Category.comp_id, Subsingleton.elim i 0]
    exact this
  · intro t m _ hπ
    have key : ∀ m : t.pt ⟶ X, m ≫ 𝟙 X = t.π 0 → m = t.π 0 := fun m h => by rwa [Category.comp_id] at h
    exact key m (hπ 0)

def ι {D E : CommRingCat.{0}} (e : D ⟶ E) : (p : ℕ) → Fin (p+1) → (E ⟶ (tp e p).1)
  | 0 => fun _ => 𝟙 E
  | p+1 => Fin.lastCases (pushout.inr (tp e p).2 e) (fun i => ι e p i ≫ pushout.inl (tp e p).2 e)

lemma ι_last {D E : CommRingCat.{0}} (e : D ⟶ E) (p : ℕ) :
    ι e (p+1) (Fin.last _) = pushout.inr (tp e p).2 e := by
  first | rfl | (dsimp only [ι]; exact Fin.lastCases_last) | (dsimp only [ι]; rw [Fin.lastCases_last])

lemma ι_cast {D E : CommRingCat.{0}} (e : D ⟶ E) (p : ℕ) (i : Fin (p+1)) :
    ι e (p+1) (Fin.castSucc i) = ι e p i ≫ pushout.inl (tp e p).2 e := by
  first | rfl | (dsimp only [ι]; exact Fin.lastCases_castSucc i) | (dsimp only [ι]; rw [Fin.lastCases_castSucc])

lemma ι_w {D E : CommRingCat.{0}} (e : D ⟶ E) : ∀ (p : ℕ) (i : Fin (p+1)), e ≫ ι e p i = (tp e p).2
  | 0, i => Category.comp_id e
  | p+1, i => by
    induction i using Fin.lastCases with
    | last => rw [ι_last]; exact pushout.condition.symm
    | cast i =>
      rw [ι_cast]
      show e ≫ ι e p i ≫ pushout.inl _ _ = (tp e p).2 ≫ pushout.inl _ _
      rw [← Category.assoc, ι_w e p i]

lemma hπE {D E : CommRingCat.{0}} (e : D ⟶ E) (p : ℕ) (i : Fin (p+1)) : y (ι e p i) ≫ y e = y (tp e p).2 := by
  rw [← y_comp, ι_w]

def limE {D E : CommRingCat.{0}} (e : D ⟶ E) : ∀ p : ℕ,
    IsLimit (WidePullbackCone.mk (f := fun _ : Fin (p+1) => y e) (y (tp e p).2) (fun i => y (ι e p i)) (hπE e p))
  | 0 => cast (congrArg IsLimit (mk_congr rfl (funext fun i => (show y (𝟙 E) = 𝟙 _ by simp [y]).symm) _ _)) (lim0 (y e))
  | p+1 => by
    have hpb := ypb (IsPushout.of_hasPushout (tp e p).2 e)
    have h' : ∀ i, (Fin.lastCases (y (pushout.inr (tp e p).2 e)) (fun i => y (pushout.inl (tp e p).2 e) ≫ y (ι e p i)) i :
        _ ⟶ _) ≫ y e = y (pushout.inl (tp e p).2 e) ≫ y (tp e p).2 := by
      intro i
      induction i using Fin.lastCases with
      | last => rw [Fin.lastCases_last]; exact hpb.w.symm
      | cast i => rw [Fin.lastCases_castSucc, Category.assoc, hπE]
    have := stepLimit (fun i => y (ι e p i)) (hπE e p) (limE e p) _ _ hpb h'
    refine cast (congrArg IsLimit (mk_congr ?_ ?_ _ _)) this
    · exact (y_comp _ _).symm
    · funext i
      induction i using Fin.lastCases with
      | last => rw [Fin.lastCases_last, ι_last]; rfl
      | cast i => rw [Fin.lastCases_castSucc, ι_cast]; exact (y_comp _ _).symm

section Y
variable {D E Y' Y'' : CommRingCat.{0}} {e : D ⟶ E} {φ' : D ⟶ Y'} {u : Y' ⟶ Y''} {φ'' : E ⟶ Y''}

def κ (hpo : IsPushout φ' e u φ'') (p : ℕ) (i : Fin (p+1)) : Y'' ⟶ pushout φ' (tp e p).2 :=
  hpo.desc (pushout.inl _ _) (ι e p i ≫ pushout.inr _ _) (by rw [← Category.assoc, ι_w]; exact pushout.condition)

lemma hπY (hpo : IsPushout φ' e u φ'') (p : ℕ) (i : Fin (p+1)) :
    y (κ hpo p i) ≫ y u = y (pushout.inl φ' (tp e p).2) := by
  rw [← y_comp, κ, hpo.inl_desc]

lemma hgi (hpo : IsPushout φ' e u φ'') (p : ℕ) (i : Fin (p+1)) :
    y (κ hpo p i) ≫ y φ'' = y (pushout.inr φ' (tp e p).2) ≫ y (ι e p i) := by
  rw [← y_comp, κ, hpo.inr_desc, y_comp]

def limY (hpo : IsPushout φ' e u φ'') (p : ℕ) :
    IsLimit (WidePullbackCone.mk (f := fun _ : Fin (p+1) => y u) (y (pushout.inl φ' (tp e p).2))
      (fun i => y (κ hpo p i)) (hπY hpo p)) :=
  baseChangeLimit (fun i => y (ι e p i)) (hπE e p) (limE e p) (ypb hpo).flip
    (ypb (IsPushout.of_hasPushout φ' (tp e p).2)).flip (fun i => y (κ hpo p i)) (hπY hpo p) (hgi hpo p)

end Y

theorem CechLevelIso_of : LateralTheory.E.LevelsPf.Tp.CechLevelIso := by
  intro p D E Y' Y'' e φ' u φ'' hpo
  let R := (limE e p).conePointUniqueUpToIso (limit.isLimit _)
  let L := (limY hpo p).conePointUniqueUpToIso (limit.isLimit _)
  have hR : ∀ j, R.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y e) j = y (ι e p j) := fun j =>
    (limE e p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)
  have hRb : R.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y e) = y (tp e p).2 :=
    (limE e p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) none
  have hL : ∀ j, L.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y u) j = y (κ hpo p j) := fun j =>
    (limY hpo p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)
  have hLb : L.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y u) = y (pushout.inl φ' (tp e p).2) :=
    (limY hpo p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) none
  have hw : L.hom ≫ (Arrow.mapCechNerve (sq e φ' u φ'' hpo.w)).app (op (SimplexCategory.mk p)) =
      y (pushout.inr φ' (tp e p).2) ≫ R.hom := by
    apply WidePullback.hom_ext
    · intro j
      simp only [Arrow.mapCechNerve_app, Category.assoc, WidePullback.lift_π]
      have key : (L.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y u) j) ≫ y φ'' =
          y (pushout.inr φ' (tp e p).2) ≫ R.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y e) j := by
        exact (congrArg (· ≫ y φ'') (hL j)).trans ((hgi hpo p j).trans
          (congrArg (y (pushout.inr φ' (tp e p).2) ≫ ·) (hR j).symm))
      rw [← Category.assoc]
      exact key
    · simp only [Arrow.mapCechNerve_app, Category.assoc, WidePullback.lift_base]
      have key : (L.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y u)) ≫ y φ' =
          y (pushout.inr φ' (tp e p).2) ≫ R.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y e) := by
        exact (congrArg (· ≫ y φ') hLb).trans (((ypb (IsPushout.of_hasPushout φ' (tp e p).2)).w).trans
          (congrArg (y (pushout.inr φ' (tp e p).2) ≫ ·) hRb.symm))
      rw [← Category.assoc]
      exact key
  exact ⟨(Arrow.isoMk (f := Arrow.mk (y (pushout.inr φ' (tp e p).2)))
    (g := Arrow.mk ((Arrow.mapCechNerve (sq e φ' u φ'' hpo.w)).app (op (SimplexCategory.mk p)))) L R hw).symm⟩

end LateralTheory.E.CechLevelIsoPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ClassSecPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.ClassSecPf

section
variable {R : Type} [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ)

abbrev S : ShortComplex (ModuleCat.{1} (ULift.{1} R)) :=
  (LateralTheory.E.LeafLocPf.secCx F X).sc' (n - 1) n (n + 1)

def fz (z : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) : (free R).obj (yoneda.obj X) ⟶ (res R F).X n :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((free R).obj (yoneda.obj X))).inv ≫ (z : Cochain _ _ n).v 0 n (zero_add n)

theorem fz_add (z w : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) :
    fz X F n (z + w) = fz X F n z + fz X F n w := by
  simp [fz]

theorem fz_mk (f : (free R).obj (yoneda.obj X) ⟶ (res R F).X n) (hf : f ≫ (res R F).d n (n + 1) = 0) :
    fz X F n (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf) = f := by
  unfold fz
  rw [Cocycle.fromSingleMk_coe]
  erw [Cochain.fromSingleMk_v f (zero_add n)]
  simp

theorem exists_mk (z : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) :
    ∃ (hf : fz X F n z ≫ (res R F).d n (n + 1) = 0),
      Cocycle.fromSingleMk (fz X F n z) (zero_add n) (n + 1) rfl hf = z := by
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective z n (zero_add n) (n + 1) rfl
  rw [fz_mk]
  exact ⟨hf, rfl⟩

variable (e : ∀ G : Shv R, ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X)
  (he : ∀ {G G' : Shv R} (φ : G ⟶ G') (f : (free R).obj (yoneda.obj X) ⟶ G), e G' (f ≫ φ) = Sec.map φ (e G f))

def ee (k : ℤ) : ((free R).obj (yoneda.obj X) ⟶ (res R F).X k) ≃+ (LateralTheory.E.LeafLocPf.secCx F X).X k :=
  e ((res R F).X k)

include he in
theorem ee_comp (i j : ℤ) (f : (free R).obj (yoneda.obj X) ⟶ (res R F).X i) :
    ee X F e j (f ≫ (res R F).d i j) = ((LateralTheory.E.LeafLocPf.secCx F X).d i j).hom (ee X F e i f) :=
  he _ f

include he in
theorem mem_ker (f : (free R).obj (yoneda.obj X) ⟶ (res R F).X n) (hf : f ≫ (res R F).d n (n + 1) = 0) :
    (show (S X F n).X₂ from ee X F e n f) ∈ LinearMap.ker (S X F n).g.hom := by
  rw [LinearMap.mem_ker]
  change ((LateralTheory.E.LeafLocPf.secCx F X).d n (n + 1)).hom (ee X F e n f) = 0
  rw [← ee_comp X F e he, hf, map_zero]

def cyc (z : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) : LinearMap.ker (S X F n).g.hom :=
  ⟨ee X F e n (fz X F n z), mem_ker X F n e he _ (exists_mk X F n z).1⟩

theorem cyc_add (z w : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) :
    cyc X F n e he (z + w) = cyc X F n e he z + cyc X F n e he w := by
  apply Subtype.ext
  change ee X F e n (fz X F n (z + w)) = ee X F e n (fz X F n z) + ee X F e n (fz X F n w)
  rw [fz_add, map_add (f := _)]

def phi : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n →+ (S X F n).moduleCatLeftHomologyData.H where
  toFun z := (LinearMap.range (S X F n).moduleCatToCycles).mkQ (cyc X F n e he z)
  map_zero' := by
    have : cyc X F n e he 0 = 0 := by
      have h := cyc_add X F n e he 0 0
      rw [add_zero] at h
      exact (add_eq_left.mp h.symm)
    rw [this, (LinearMap.range (S X F n).moduleCatToCycles).mkQ.map_zero]
  map_add' z w := by
    rw [cyc_add, (LinearMap.range (S X F n).moduleCatToCycles).mkQ.map_add]

theorem phi_eq_zero_iff (z : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) :
    phi X F n e he z = 0 ↔ z ∈ coboundaries _ _ _ := by
  obtain ⟨hf, hz⟩ := exists_mk X F n z
  have key : z ∈ coboundaries (LateralTheory.E.LocSecPf.pt R X) (res R F) n ↔
      ∃ g : (free R).obj (yoneda.obj X) ⟶ (res R F).X (n - 1), g ≫ (res R F).d (n - 1) n = fz X F n z := by
    conv_lhs => rw [← hz]
    exact Cocycle.fromSingleMk_mem_coboundaries_iff (K := res R F) (fz X F n z) (zero_add n) (n + 1) rfl hf
      (n - 1) (by omega)
  rw [key]
  change (LinearMap.range (S X F n).moduleCatToCycles).mkQ (cyc X F n e he z) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(ee X F e (n - 1)).symm s, (ee X F e n).injective ?_⟩
    rw [ee_comp X F e he]; erw [AddEquiv.apply_symm_apply]
    exact congrArg Subtype.val hs
  · rintro ⟨g, hg⟩
    refine ⟨ee X F e (n - 1) g, Subtype.ext ?_⟩
    change ((LateralTheory.E.LeafLocPf.secCx F X).d (n - 1) n).hom (ee X F e (n - 1) g) = ee X F e n (fz X F n z)
    rw [← ee_comp X F e he, hg]

def psi : CohomologyClass (LateralTheory.E.LocSecPf.pt R X) (res R F) n →+ (S X F n).moduleCatLeftHomologyData.H :=
  CohomologyClass.descAddMonoidHom (phi X F n e he) (fun z hz => (phi_eq_zero_iff X F n e he z).2 hz)

theorem psi_bijective : Function.Bijective (psi X F n e he) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective c
    rw [CohomologyClass.mk_eq_zero_iff, ← phi_eq_zero_iff X F n e he]
    exact hc
  · intro c
    obtain ⟨⟨s, hs⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have hf : (ee X F e n).symm s ≫ (res R F).d n (n + 1) = 0 := by
      apply (ee X F e (n + 1)).injective
      rw [ee_comp X F e he, map_zero]; erw [AddEquiv.apply_symm_apply]
      exact hs
    refine ⟨CohomologyClass.mk (Cocycle.fromSingleMk _ (zero_add n) (n + 1) rfl hf), ?_⟩
    change (LinearMap.range (S X F n).moduleCatToCycles).mkQ (cyc X F n e he _) = Submodule.Quotient.mk _
    rw [Submodule.mkQ_apply]
    congr 1
    apply Subtype.ext
    change ee X F e n (fz X F n _) = s
    rw [fz_mk]
    exact (ee X F e n).apply_symm_apply s

end

theorem classSec : LateralTheory.E.LocSecPfB.ClassSec := by
  intro R _ X e he F n
  refine ⟨(AddEquiv.ofBijective _ (psi_bijective X F n e he)).trans ?_⟩
  exact ((LateralTheory.E.LeafLocPf.secCx F X).homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp) ≪≫
    (S X F n).moduleCatHomologyIso).toLinearEquiv.toAddEquiv.symm

theorem ClassSec_of : LateralTheory.E.LocSecPfB.ClassSec := classSec

end LateralTheory.E.ClassSecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DegreeZeroGenerators
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.DegreeZeroGenerators
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafShMapZeroPf LateralTheory.E.LeafShMapZeroPf.Gen

abbrev Rq (q : ℕ) := ULift.{1} (ZMod q)

abbrev Gq (q : ℕ) : Type 0 ⥤ ModuleCat.{1} (Rq q) := uliftFunctor.{1, 0} ⋙ ModuleCat.free (Rq q)

abbrev P0 (B : Scheme.{0}) (q : ℕ) (U : B.Etale) : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (Rq q) :=
  ((Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (Rq q))).obj (Gq q)).obj (yoneda.obj U)

def gen {B : Scheme.{0}} {q : ℕ} (U : B.Etale) : ((F0 B q).obj U).obj.obj (op U) :=
  (toSheafify (EtTop B) (P0 B q U)).app (op U) (ModuleCat.freeMk (ULift.up (𝟙 U)))

theorem gen_nat {B : Scheme.{0}} {q : ℕ} {U U' : B.Etale} (a : U' ⟶ U) :
    ((F0 B q).map a).hom.app (op U') (gen U') = ((F0 B q).obj U).obj.map a.op (gen U) := by
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality (EtTop B)
    (((Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (Rq q))).obj (Gq q)).map (yoneda.map a))) (op U'))
    (ModuleCat.freeMk (ULift.up (𝟙 U')))
  have h2 := ConcreteCategory.congr_hom ((toSheafify (EtTop B) (P0 B q U)).naturality a.op)
    (ModuleCat.freeMk (ULift.up (𝟙 U)))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h1 h2
  unfold gen
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · rfl
  · refine Eq.trans ?_ h2
    congr 1
    simp only [Gq, Functor.comp_map]
    erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply]
    show ModuleCat.freeMk (ULift.up (𝟙 U' ≫ a)) = ModuleCat.freeMk (ULift.up (a ≫ 𝟙 U))
    simp

theorem free_etale_sheaf_zmod_exists_hom_sending_generator {B : Scheme.{0}} {q : ℕ} (H : SShv B q) (U : B.Etale) (x : H.obj.obj (op U)) :
    ∃ t : (F0 B q).obj U ⟶ H, t.hom.app (op U) (gen U) = x := by
  let φ : P0 B q U ⟶ H.obj :=
    { app := fun W => ModuleCat.freeDesc (TypeCat.ofHom (fun f : ULift.{1} (W.unop ⟶ U) => H.obj.map f.down.op x))
      naturality := by
        intro W W' f
        apply ModuleCat.free_hom_ext
        intro y
        simp only [Gq, ConcreteCategory.comp_apply, Functor.comp_map]
        erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        show H.obj.map (f.unop ≫ y.down).op x = H.obj.map f (H.obj.map y.down.op x)
        simp }
  refine ⟨((sheafificationAdjunction (EtTop B) _).homEquiv (P0 B q U) H).symm φ, ?_⟩
  have e := ((sheafificationAdjunction (EtTop B) _).homEquiv (P0 B q U) H).apply_symm_apply φ
  rw [Adjunction.homEquiv_unit] at e
  have e2 := ConcreteCategory.congr_hom (NatTrans.congr_app e (op U)) (ModuleCat.freeMk (ULift.up (𝟙 U)))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at e2
  unfold gen
  refine Eq.trans ?_ (e2.trans ?_)
  · rfl
  · simp only [φ]
    erw [ModuleCat.freeDesc_apply]
    show H.obj.map (𝟙 U).op x = x
    simp

theorem free_etale_sheaf_zmod_representable_generates : EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerators := by
  intro B q H H' g h
  apply (sheafToPresheaf (EtTop B) (ModuleCat.{1} (Rq q))).map_injective
  rw [Functor.map_zero]
  apply NatTrans.ext
  funext U
  induction U with | op U => ?_
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨t, ht⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator H U x
  obtain ⟨S, hS, hP⟩ := h U t
  have key : ∀ (U' : B.Etale) (a : U' ⟶ U), S a →
      H'.obj.map a.op (g.hom.app (op U) x) = H'.obj.map a.op 0 := by
    intro U' a ha
    have h3 := congrArg (fun m : (F0 B q).obj U' ⟶ H' =>
      ((sheafToPresheaf (EtTop B) (ModuleCat.{1} (Rq q))).map m).app (op U') (gen U')) (hP U' a ha)
    simp only [Functor.map_comp, Functor.map_zero, NatTrans.comp_app, NatTrans.app_zero,
      ConcreteCategory.comp_apply] at h3
    rw [map_zero, ← ht]
    have n := ConcreteCategory.congr_hom (g.hom.naturality a.op) (t.hom.app (op U) (gen U))
    simp only [ConcreteCategory.comp_apply] at n
    rw [← n]
    have n2 := ConcreteCategory.congr_hom (t.hom.naturality a.op) (gen U)
    simp only [ConcreteCategory.comp_apply] at n2
    rw [← n2, ← gen_nat a]
    exact h3
  have := Sheaf.isSeparated H' U S hS _ 0 key
  simp only [NatTrans.app_zero]
  exact this

end LateralTheory.E.DegreeZeroGenerators
end
end

