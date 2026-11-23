module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.ThetaFn

open CubeValues SymmetricSemicharacter

section Values

variable {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X)

def valHom (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valAt'_eq_valHom {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = valHom x U h f := by
  rw [valAt', dite_eq_left h]; rfl

theorem valAt'_mul {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)) :
    valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  simp only [valAt'_eq_valHom x h, map_mul]

theorem valAt'_unit_zpow {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) (k : ℤ) :
    valAt' x U (f ^ k).val = valAt' x U f.val ^ k := by
  simp only [valAt'_eq_valHom x h]
  have h1 : ∀ v : Γ(X, U)ˣ, valHom x U h v.val =
      ((Units.coeHom ℂ).comp (Units.map (valHom x U h).toMonoidHom)) v := fun v => rfl
  simp only [h1, map_zpow]

theorem valAt'_res {U V : X.Opens} (h : V ≤ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valAt' x V ((X.presheaf.map (homOfLE h).op).hom f) = valAt' x U f :=
  (valueRules X x).2.2.1 U V h f hV

theorem valAt'_app (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f :=
  (valueRules X x).2.2.2.1 Y φ U f

theorem valAt'_appLE' (φ : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V ≤ φ ⁻¹ᵁ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, U)) :
    valAt' x V ((φ.appLE U V e).hom f) = valAt' (x ≫ φ) U f :=
  (valAt'_res x e hV _).trans (valAt'_app x φ U f)

theorem valAt'_sec {M : LB X} (s : M.Sec) (i j : M.ι) (hi : ⊤ ≤ x ⁻¹ᵁ M.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ M.U j) :
    valAt' x (M.U i) (s.f i) =
      valAt' x (M.U i ⊓ M.U j) (M.g i j).val * valAt' x (M.U j) (s.f j) := by
  have hij := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  rw [← valAt'_res x inf_le_left hij (s.f i), s.compat i j, valAt'_mul x hij,
    valAt'_res x inf_le_right hij]

theorem valAt'_id_top (r : Γ(Sp ℂ, ⊤)) :
    valAt' (𝟙 (Sp ℂ)) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom r := by
  have e : ∀ k, Scheme.Hom.appLE (𝟙 (Sp ℂ)) ⊤ ⊤ k = 𝟙 _ := fun k => by
    rw [← Scheme.Hom.id_app]
    exact (Scheme.Hom.app_eq_appLE (𝟙 (Sp ℂ)) (U := ⊤)).symm
  rw [valAt', dite_eq_left (show ⊤ ≤ 𝟙 (Sp ℂ) ⁻¹ᵁ ⊤ from fun _ _ => trivial), valAt, e]
  rfl

end Values

section Transport

variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] [Unique K]
  [Unique K']

theorem res_appLE (h : Z ⟶ Y) {U U' : Y.Opens} {V V' : Z.Opens} (hU : U' ≤ U) (hV : V' ≤ V)
    (e : V ≤ h ⁻¹ᵁ U) (e' : V' ≤ h ⁻¹ᵁ U') (f : Γ(Y, U)) :
    (Z.presheaf.map (homOfLE hV).op).hom ((h.appLE U V e).hom f) =
      (h.appLE U' V' e').hom ((Y.presheaf.map (homOfLE hU).op).hom f) :=
  congrArg (fun t : Γ(Y, U) ⟶ Γ(Z, V') => t.hom f)
    ((Scheme.Hom.appLE_map h e (homOfLE hV).op).trans
      (Scheme.Hom.map_appLE h e' (homOfLE hU).op).symm)


omit [Unique K] in
theorem wchart_le_of_comp {φ : Y ⟶ X} {ψ : Z ⟶ X} {h : Z ⟶ Y} (e : h ≫ φ = ψ) (j : K' → L.ι) :
    LB.wchart L (fun _ : K' => ψ) j ≤
      h ⁻¹ᵁ LB.wchart L (fun _ : K => φ) (fun _ => j default) := by
  subst e
  exact fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy default

theorem le_wchart_unique {W : Scheme.{0}} (x : W ⟶ Y) (φ : Y ⟶ X) (j : K → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : K => φ) j ↔ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (j default) :=
  ⟨fun h _ hy => Set.mem_iInter.1 (h hy) default, fun h _ hy => Set.mem_iInter.2 fun k => by
    rw [Subsingleton.elim k default]; exact h hy⟩

def pullPow {φ : Y ⟶ X} {ψ : Z ⟶ X} (h : Z ⟶ Y) (e : h ≫ φ = ψ) (a : ℤ)
    (s : LB.Sec (LB.LinComb L (fun _ : K => φ) (fun _ => a))) :
    LB.Sec (LB.LinComb L (fun _ : K' => ψ) (fun _ => a)) where
  f j := (h.appLE _ _ (wchart_le_of_comp L (K := K) e j)).hom (s.f (fun _ => j default))
  compat i j := by
    have hij : LB.wchart L (fun _ : K' => ψ) i ⊓ LB.wchart L (fun _ : K' => ψ) j ≤
        h ⁻¹ᵁ (LB.wchart L (fun _ : K => φ) (fun _ => i default) ⊓
          LB.wchart L (fun _ : K => φ) (fun _ => j default)) :=
      le_inf (inf_le_left.trans (wchart_le_of_comp L e i))
        (inf_le_right.trans (wchart_le_of_comp L e j))
    have hc := congrArg (h.appLE _ _ hij).hom (s.compat (fun _ => i default) (fun _ => j default))
    replace hc := hc.trans (map_mul (h.appLE _ _ hij).hom _ _)
    have hg : (h.appLE _ _ hij).hom ((LB.LinComb L (fun _ : K => φ) (fun _ => a)).g
        (fun _ => i default) (fun _ => j default)).val =
        ((LB.LinComb L (fun _ : K' => ψ) (fun _ => a)).g i j).val := by
      subst e
      change (Units.map (h.appLE _ _ hij).hom.toMonoidHom _).val = _
      congr 1
      simp only [LB.LinComb, Fintype.prod_unique, map_zpow]
      congr 1
      ext1
      exact congrArg (fun t => t.hom (L.g (i default) (j default)).val)
        (Scheme.Hom.appLE_comp_appLE h φ _ _ _ _ hij)
    refine Eq.trans ?_ (hc.trans (congrArg₂ (· * ·) hg ?_))
    · exact res_appLE h _ _ _ hij _
    · exact (res_appLE h _ _ _ hij _).symm

end Transport

section Fibre

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)


variable (A) in
def fibreIncl : A ⟶ T ⊗ A := lift (toUnit A ≫ p) (𝟙 A)




def exAt (z : Fin g → ℂ) : Sp ℂ ⟶ (T ⊗ A).left := (lift p (u.ex z)).left

theorem exAt_snd (z : Fin g → ℂ) : exAt u p z ≫ (snd T A).left = (u.ex z).left :=
  (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_snd p (u.ex z)))

theorem exAt_fst (z : Fin g → ℂ) : exAt u p z ≫ (fst T A).left = p.left :=
  (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_fst p (u.ex z)))

theorem ex_fibreIncl (z : Fin g → ℂ) : (u.ex z).left ≫ (fibreIncl A p).left = exAt u p z := by
  rw [← Over.comp_left, fibreIncl, comp_lift, Category.comp_id, ← Category.assoc,
    toUnit_unique (u.ex z ≫ toUnit A) (𝟙 _), Category.id_comp]
  rfl

theorem exAt_add_period (z l : Fin g → ℂ) (hl : l ∈ u.Λ) : exAt u p (z + l) = exAt u p z := by
  rw [exAt, exAt, ex_add_period u z l hl]

theorem comp_ptSecT {x : T ⟶ A} {z : Fin g → ℂ} (hx : p ≫ x = u.ex z) :
    p.left ≫ (ptSecT A x).left = exAt u p z := by
  rw [← Over.comp_left, ptSecT, comp_lift, Category.comp_id, hx]
  rfl

theorem exAt_mem_chart_iff (k : ℤ) (j : Fin 1 → L.ι) (z : Fin g → ℂ) :
    ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j ↔ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) := by
  refine (le_wchart_unique L (exAt u p z) (snd T A).left j).trans ?_
  rw [exAt_snd]
  rfl

theorem exAt_hol (U : (T ⊗ A).left.Opens) (f : Γ((T ⊗ A).left, U)) :
    IsOpen {z | ⊤ ≤ exAt u p z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (exAt u p z) U f) {z | ⊤ ≤ exAt u p z ⁻¹ᵁ U} := by
  have h := u.hol ((fibreIncl A p).left ⁻¹ᵁ U) (((fibreIncl A p).left.app U).hom f)
  simp only [← ex_fibreIncl]
  refine ⟨h.1, h.2.congr fun z _ => ?_⟩
  exact (valAt'_app (u.ex z).left (fibreIncl A p).left U f).symm

theorem valAt'_liftFun {W : (T ⊗ A).left.Opens} {z : Fin g → ℂ} (hW : ⊤ ≤ exAt u p z ⁻¹ᵁ W)
    (r : Γ(T.left, ⊤)) : valAt' (exAt u p z) W (liftFun A W r) = valAt' p.left ⊤ r := by
  refine (valAt'_res (exAt u p z) (U := (fst T A).left ⁻¹ᵁ ⊤) le_top hW _).trans ?_
  refine (valAt'_app (exAt u p z) (fst T A).left ⊤ r).trans ?_
  rw [exAt_fst]

theorem valAt'_LPow_g (k : ℤ) (j j' : Fin 1 → L.ι) (z : Fin g → ℂ)
    (hj : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j) (hj' : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j') :
    valAt' (exAt u p z) ((LPow A L k T).U j ⊓ (LPow A L k T).U j') ((LPow A L k T).g j j').val =
      valAt' (u.ex z).left (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)).val ^ k := by
  refine (val_linComb (exAt u p z) valueRules L _ _ j j' hj hj').trans ?_
  rw [Fin.prod_univ_one, exAt_snd]

def IsFnAt (k : ℤ) (s : LB.Sec (LPow A L k T)) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (j : Fin 1 → L.ι) z, ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j →
    valAt' (exAt u p z) ((LPow A L k T).U j) (s.f j) = θ z * u.fr (j 0) z ^ k

theorem exists_chart_exAt (hL : L.IsLB) (k : ℤ) (z : Fin g → ℂ) :
    ∃ j : Fin 1 → L.ι, ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL z
  exact ⟨fun _ => i, (exAt_mem_chart_iff u p k _ z).2 hi⟩

theorem fr_zpow_ne_zero {k : ℤ} {j : Fin 1 → L.ι} {z : Fin g → ℂ}
    (hj : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j) (m : ℤ) : u.fr (j 0) z ^ m ≠ 0 :=
  zpow_ne_zero m (u.fr_ne _ z ((exAt_mem_chart_iff u p k j z).1 hj))


variable {u p} in
theorem IsFnAt.eq_div {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) {j : Fin 1 → L.ι} {z : Fin g → ℂ}
    (hj : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j) :
    θ z = valAt' (exAt u p z) ((LPow A L k T).U j) (s.f j) / u.fr (j 0) z ^ k := by
  rw [h j z hj, mul_div_cancel_right₀ _ (fr_zpow_ne_zero u p hj k)]

theorem isFnAt_of_exists_chart {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : ∀ z, ∃ j : Fin 1 → L.ι, ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j ∧
      valAt' (exAt u p z) ((LPow A L k T).U j) (s.f j) = θ z * u.fr (j 0) z ^ k) :
    IsFnAt u p k s θ := by
  intro j z hj
  obtain ⟨j', hj', e⟩ := h z
  have hc := u.fr_compat (j 0) (j' 0) z ((le_preimage_inf _ _ _).2
    ⟨(exAt_mem_chart_iff u p k j z).1 hj, (exAt_mem_chart_iff u p k j' z).1 hj'⟩)
  rw [valAt'_sec _ s j j' hj hj', valAt'_LPow_g u p k j j' z hj hj', e, hc, mul_zpow]
  ring


variable {u p} in
theorem IsFnAt.unique (hL : L.IsLB) {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {θ θ' : (Fin g → ℂ) → ℂ} (h : IsFnAt u p k s θ) (h' : IsFnAt u p k s θ') : θ = θ' := by
  funext z
  obtain ⟨j, hj⟩ := exists_chart_exAt u p hL k z
  rw [h.eq_div hj, h'.eq_div hj]

theorem existsUnique_isFnAt (hL : L.IsLB) (k : ℤ) (s : LB.Sec (LPow A L k T)) :
    ∃! θ, IsFnAt u p k s θ := by
  choose c hc using exists_chart_exAt u p hL k
  have h : IsFnAt u p k s fun z =>
      valAt' (exAt u p z) ((LPow A L k T).U (c z)) (s.f (c z)) / u.fr (c z 0) z ^ k :=
    isFnAt_of_exists_chart u p fun z =>
      ⟨c z, hc z, (div_mul_cancel₀ _ (fr_zpow_ne_zero u p (hc z) k)).symm⟩
  exact ⟨_, h, fun θ hθ => hθ.unique hL h⟩

def fnAt (hL : L.IsLB) (k : ℤ) (s : LB.Sec (LPow A L k T)) : (Fin g → ℂ) → ℂ :=
  (existsUnique_isFnAt u p hL k s).exists.choose

theorem isFnAt_fnAt (hL : L.IsLB) (k : ℤ) (s : LB.Sec (LPow A L k T)) :
    IsFnAt u p k s (fnAt u p hL k s) :=
  (existsUnique_isFnAt u p hL k s).exists.choose_spec

variable {u p}

variable (u p)

theorem isFnAt_zero (k : ℤ) : IsFnAt u p k (H1.SectionArithmetic.secZero (LPow A L k T)) 0 := fun j z hj => by
  rw [Pi.zero_apply, zero_mul, valAt'_eq_valHom _ hj]
  exact map_zero _


variable (A L) in
def secOfFun (r : Γ(T.left, ⊤)) : LB.Sec (LPow A L 0 T) where
  f j := liftFun A _ r
  compat j j' := by
    have : (LPow A L 0 T).g j j' = 1 := by
      unfold LPow LB.LinComb
      dsimp only
      exact Finset.prod_eq_one fun _ _ => zpow_zero _
    rw [this, Units.val_one, _root_.one_mul]
    exact (res_liftHom A _ r).trans (res_liftHom A _ r).symm

theorem isFnAt_secOfFun (r : Γ(T.left, ⊤)) :
    IsFnAt u p 0 (secOfFun A L r) (fun _ => valAt' p.left ⊤ r) := fun j z hj => by
  rw [zpow_zero, _root_.mul_one]
  exact valAt'_liftFun u p hj r






variable {u p}

theorem mem_ptChart_iff {x : T ⟶ A} {z : Fin g → ℂ} (hx : p ≫ x = u.ex z) (j : Fin 1 → L.ι) :
    ⊤ ≤ p.left ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => x.left) j ↔ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) := by
  refine (le_wchart_unique L p.left x.left j).trans ?_
  rw [← Over.comp_left, hx]
  rfl


variable (u p) in
theorem comp_one_eq_ex_zero : p ≫ (1 : T ⟶ A) = u.ex 0 := by
  rw [ex_zero, MonObj.comp_one]


variable (p) in
theorem valAt'_rigT {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig) (k : ℤ)
    (j : Fin 1 → L.ι) (hj : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ L.U (j 0)) :
    valAt' p.left (LB.wchart L (fun _ : Fin 1 => (1 : T ⟶ A).left) j)
      ((rigT A L rig T k).s j).val = u.fr (j 0) 0 ^ k := by
  have hj' := (mem_ptChart_iff (comp_one_eq_ex_zero u p) j).2 hj
  have hp : p.left ≫ T.hom = 𝟙 (Sp ℂ) := Over.w p
  have h0 : ⊤ ≤ (L.pull (eSec A)).U (fun _ => j 0) := by
    rw [ex_zero] at hj
    exact fun _ hy => Set.mem_iInter.2 fun _ => hj hy
  refine (valAt'_unit_zpow p.left hj' _ k).trans (congrArg (· ^ k) ?_)
  refine (valAt'_appLE' p.left T.hom (rigT_le A L j) hj' _).trans ?_
  rw [hp]
  exact (hrig (fun _ => j 0) h0).symm

theorem IsFnAt.twistPull {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)} {θ θ' : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p b s θ) (h' : IsFnAt u p a s' θ') (ht : IsTwistPull A L ψ m hm a b α s s')
    {z w : Fin g → ℂ} (hw : exAt u p z ≫ ψ.left = exAt u p w) (j : Fin 2 → L.ι)
    (hj : ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j) :
    θ' z * u.fr (j 0) z ^ a =
      valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
        (θ w * u.fr (j 1) w ^ b) := by
  have h0 : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L a T).U (fun _ => j 0) :=
    fun _ hy => chart_le_zero A L m j (hj hy)
  have h1 : ⊤ ≤ exAt u p w ⁻¹ᵁ (LPow A L b T).U (fun _ => j 1) := by
    rw [← hw]
    exact fun _ hy => chart_le_pull A L ψ m hm j (hj hy)
  refine (h' _ z h0).symm.trans ((valAt'_res _ (chart_le_zero A L m j) hj _).symm.trans ?_)
  refine (congrArg _ (ht j)).trans ((valAt'_mul _ hj _ _).trans (congrArg (_ * ·) ?_))
  refine (valAt'_appLE' _ ψ.left (chart_le_pull A L ψ m hm j) hj _).trans ?_
  rw [hw]
  exact h _ w h1

end Fibre

section Base

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

def basePt : 𝟙_ (Over (Sp ℂ)) ⟶ baseOver (Sp ℂ) := Over.homMk (𝟙 (Sp ℂ)) (Category.id_comp _)

instance isIso_basePt : IsIso basePt := inferInstanceAs (IsIso (𝟙 (𝟙_ (Over (Sp ℂ)))))

abbrev IsFnT (k : ℤ) (s : LB.Sec (LPow A L k (baseOver (Sp ℂ)))) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  IsFnAt u basePt k s θ

abbrev constT (a : ℂ) : Γ((baseOver (Sp ℂ)).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a

abbrev numT (r : Γ((baseOver (Sp ℂ)).left, ⊤)) : ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom r

theorem numT_constT (a : ℂ) : numT (constT a) = a :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply a

theorem valAt'_basePt (r : Γ((baseOver (Sp ℂ)).left, ⊤)) : valAt' basePt.left ⊤ r = numT r :=
  valAt'_id_top r

variable {u}

variable (u)

theorem isFnT_zero (k : ℤ) :
    IsFnT u k (H1.SectionArithmetic.secZero (LPow A L k (baseOver (Sp ℂ)))) 0 := isFnAt_zero u basePt k

theorem isFnT_const (a : ℂ) : IsFnT u 0 (secOfFun A L (constT a)) (fun _ => a) := by
  have h := isFnAt_secOfFun u basePt (constT a)
  rwa [valAt'_basePt, numT_constT] at h

end Base

def zeroUnif : HolUnif (Inh.zeroPolAV (Sp ℂ)).A (Inh.zeroPolAV (Sp ℂ)).L 0 where
  ex _ := 1
  ex_add _ _ := (_root_.mul_one _).symm
  ex_onto x := ⟨0, toUnit_unique _ _⟩
  Λ := ⊤
  ker _ := ⟨fun _ => trivial, fun _ => rfl⟩
  discrete := inferInstance
  full := by simp
  hol _ _ := ⟨isOpen_discrete _, differentiableOn_const _⟩
  fr _ _ := 1
  fr_hol _ := differentiableOn_const _
  fr_ne _ _ _ := one_ne_zero
  fr_compat _ _ _ h := by
    rw [valAt'_eq_valHom _ h, _root_.mul_one]
    exact (map_one _).symm

end GlobalTheory.ThetaFn
