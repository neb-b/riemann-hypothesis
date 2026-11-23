module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVPf
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

def PullCubDescentSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    IsAdicComplete (maximalIdeal V) V →
    ∀ (t t' : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V))), IsProper tK.G.hom →
    ∀ (m : SABMap tK t (spMap (algebraMap V (FractionRing V))))
      (m' : SABMap tK t' (spMap (algebraMap V (FractionRing V)))) (ψ : t.G ⟶ t'.G) [IsMonHom ψ],
      m.φ ≫ ψ.left = m'.φ → (CubeMap.ofHom ψ).IsPullCubical t.cub t'.cub

theorem extV_of (hHom : HomExtDvrSt) (hD : PullCubDescentSt) : ExtVStatement := by
  intro E _ _ _ H V _ _ _ hc t t' tK hK m m'
  obtain ⟨ψ, hψm, hψ, hact⟩ := extV_grp hHom t t' tK m m'
  have := hψm
  refine ⟨{ cm := CubeMap.ofHom ψ.hom
            cart := isGrpPullback_of_iso ψ
            base := rfl
            act := fun a => by
              show (t.act.act a).left ≫ ψ.hom.left = ψ.hom.left ≫ (t'.act.act a).left
              rw [← Over.comp_left, hact a, Over.comp_left]
            lin := hD E H V hc t t' tK hK m m' ψ.hom hψ }, hψ⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj

variable {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G']
  {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ)
include h

theorem inj_over {T : Over (Sp S)} {u v : T ⟶ G'} (e : u.left ≫ φ = v.left ≫ φ) : u = v := Over.OverMorphism.ext (h.1.hom_ext e (by simp))

theorem tan_push (w : epsR S ⟶ G') : IsTangent w ↔
    Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w.left ≫ φ = (1 : Over.mk x ⟶ G).left := by
  have oneL : ∀ {Y : Scheme.{0}} (T H : Over Y) [GrpObj H], (1 : T ⟶ H).left = T.hom ≫ η[H].left := by
    intro Y T H _
    show (toUnit T ≫ η[H]).left = _
    rw [Over.comp_left]
    congr 1
    all_goals first
      | simpa using Over.w (toUnit T)
      | (have e := Over.w (toUnit T)
         rwa [show (𝟙_ (Over Y)).hom = 𝟙 Y from rfl, Category.comp_id] at e)
  have hmul : ∀ {T : Over (Sp S)} (a b : T ⟶ G'), pushPt h.1.w (a * b) = pushPt h.1.w a * pushPt h.1.w b :=
    fun {T} a b => Over.OverMorphism.ext (h.2 T a b (pushPt h.1.w a) (pushPt h.1.w b) rfl rfl).symm
  have hone : ∀ T : Over (Sp S), pushPt h.1.w (1 : T ⟶ G') = 1 := by
    intro T
    have e1 : pushPt h.1.w (1 : T ⟶ G') * pushPt h.1.w 1 = pushPt h.1.w 1 := by
      rw [← hmul, _root_.one_mul]
    exact mul_right_cancel (e1.trans (_root_.one_mul _).symm)
  have hη : η[G'].left ≫ φ = x ≫ η[G].left := by
    have e := congrArg (fun g => g.left) (hone (Over.mk (𝟙 (Sp S))))
    simp only [pushPt, Over.homMk_left, oneL, Over.mk_hom] at e
    simpa using e
  have hfa : Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (epsR S).hom = 𝟙 _ := by
    simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
    rw [← Spec.map_id]
    congr 1
    all_goals
      ext r
      first
        | (simp [TrivSqZeroExt.algebraMap_eq_inl]; done)
        | (simp; done)
  let t : Over.mk (𝟙 (Sp S)) ⟶ epsR S :=
    Over.homMk (Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom) hfa
  rw [oneL]
  simp only [Over.mk_hom]
  constructor
  · intro hw
    unfold IsTangent at hw
    rw [← Category.assoc, hw, hη]
  · intro hw
    unfold IsTangent
    have key : t ≫ w = 1 := by
      apply inj_over h
      show Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w.left ≫ φ = _
      rw [hw, oneL, Category.assoc, hη]
      simp
    have e := congrArg (fun g => g.left) key
    simp only [Over.comp_left, t, Over.homMk_left, oneL, Over.mk_hom] at e
    simpa using e

theorem prod_push {n : ℕ} {T : Over (Sp S)} (u : Fin n → (T ⟶ G')) :
    (List.ofFn u).prod.left ≫ φ = (List.ofFn fun i => pushPt h.1.w (u i)).prod.left := by
  have hmul : ∀ a b : T ⟶ G', pushPt h.1.w (a * b) = pushPt h.1.w a * pushPt h.1.w b := fun a b =>
    Over.OverMorphism.ext (h.2 T a b (pushPt h.1.w a) (pushPt h.1.w b) rfl rfl).symm
  have hone : pushPt h.1.w (1 : T ⟶ G') = 1 := by
    have e1 : pushPt h.1.w (1 : T ⟶ G') * pushPt h.1.w 1 = pushPt h.1.w 1 := by
      rw [← hmul, _root_.one_mul]
    exact mul_right_cancel (e1.trans (_root_.one_mul _).symm)
  have key : ∀ {m : ℕ} (v : Fin m → (T ⟶ G')),
      pushPt h.1.w (List.ofFn v).prod = (List.ofFn fun i => pushPt h.1.w (v i)).prod := by
    intro m
    induction m with
    | zero => intro v; simp only [List.ofFn_zero, List.prod_nil]; exact hone
    | succ m ih => intro v; simp only [List.ofFn_succ, List.prod_cons]; rw [hmul, ih]
  exact congrArg (fun f => f.left) (key u)

theorem comb_push {n : ℕ} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) (w : epsR S ⟶ G') : IsLieComb c v w ↔
    ∃ u : Fin n → (Over.mk (Geo.Tor.spMap (algebraMap S (DualNumber S)) ≫ x) ⟶ G),
      (∀ i, (u i).left = Geo.Tor.spMap (epsScaleR (c i)) ≫ (v i).left ≫ φ) ∧ (List.ofFn u).prod.left = w.left ≫ φ := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => pushPt h.1.w (u i), fun i => ?_, (prod_push h u).symm⟩
    simp [pushPt, hu i]
  · rintro ⟨u, hu, hw⟩
    have hs : ∀ i, Geo.Tor.spMap (epsScaleR (c i)) ≫ (epsR S).hom = (epsR S).hom := by
      intro i
      simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
      congr 1
      ext r <;> first | simp [epsScaleR] | simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
    let u' : Fin n → (epsR S ⟶ G') := fun i =>
      Over.homMk (Geo.Tor.spMap (epsScaleR (c i)) ≫ (v i).left) (by rw [Category.assoc, Over.w (v i)]; exact hs i)
    refine ⟨u', fun i => rfl, ?_⟩
    apply inj_over h
    have e : (fun i => pushPt h.1.w (u' i)) = u :=
      funext fun i => Over.OverMorphism.ext (by simp [pushPt, u', hu i])
    rw [prod_push h u', ← hw, e]

omit h in
theorem comb_baseChange {R : Type} [CommRing R] {G₀ : Over (Sp R)} [GrpObj G₀] (f : R →+* S) {ψ : G'.left ⟶ G₀.left}
    (h : IsGrpPullback G' G₀ (Geo.Tor.spMap f) ψ) {n : ℕ} {c : Fin n → R} {v : Fin n → (epsR R ⟶ G₀)} {w : epsR R ⟶ G₀}
    (hc : IsLieComb c v w) {v' : Fin n → (epsR S ⟶ G')} {w' : epsR S ⟶ G'}
    (hv : ∀ i, (v' i).left ≫ ψ = Geo.Tor.spMap (dualMapR f) ≫ (v i).left)
    (hw : w'.left ≫ ψ = Geo.Tor.spMap (dualMapR f) ≫ w.left) : IsLieComb (fun i => f (c i)) v' w' := by
  obtain ⟨u, hu, rfl⟩ := hc
  have hs : ∀ s : S, Geo.Tor.spMap (epsScaleR s) ≫ (epsR S).hom = (epsR S).hom := by
    intro s
    simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
    congr 1
    ext r <;> first | simp [epsScaleR] | simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hd : Geo.Tor.spMap (dualMapR f) ≫ (epsR R).hom = (epsR S).hom ≫ Geo.Tor.spMap f := by
    simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
    congr 1
    ext r <;> first
      | (simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl]; done)
      | (simp [dualMapR]; done)
      | simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl]
  have hcomm : ∀ i, Geo.Tor.spMap (dualMapR f) ≫ Geo.Tor.spMap (epsScaleR (c i)) =
      Geo.Tor.spMap (epsScaleR (f (c i))) ≫ Geo.Tor.spMap (dualMapR f) := by
    intro i
    simp only [Geo.Tor.spMap, ← Spec.map_comp]
    congr 1
    ext a <;> first
      | (simp [dualMapR, epsScaleR]; done)
      | (simp [dualMapR, epsScaleR, smul_eq_mul, map_mul]; done)
      | (simp [dualMapR, epsScaleR, smul_eq_mul, map_mul, mul_comm]; done)
      | (simp [dualMapR, epsScaleR, smul_eq_mul, map_mul, TrivSqZeroExt.algebraMap_eq_inl]; done)
      | (simp [dualMapR, epsScaleR, smul_eq_mul, TrivSqZeroExt.algebraMap_eq_inl]; clear * -; done)
  let d : Over.mk ((epsR S).hom ≫ Geo.Tor.spMap f) ⟶ epsR R := Over.homMk (Geo.Tor.spMap (dualMapR f)) hd
  have cm : ∀ a b : epsR R ⟶ G₀, d ≫ (a * b) = (d ≫ a) * (d ≫ b) := fun a b => by
    show d ≫ (lift a b ≫ μ) = lift (d ≫ a) (d ≫ b) ≫ μ
    rw [comp_lift_assoc]
  have c1 : d ≫ (1 : epsR R ⟶ G₀) = 1 := by
    show d ≫ (toUnit _ ≫ η) = toUnit _ ≫ η
    rw [comp_toUnit_assoc]
  have key : ∀ {m : ℕ} (a : Fin m → (epsR R ⟶ G₀)),
      d ≫ (List.ofFn a).prod = (List.ofFn fun i => d ≫ a i).prod := by
    intro m
    induction m with
    | zero => intro a; simp only [List.ofFn_zero, List.prod_nil]; exact c1
    | succ m ih => intro a; simp only [List.ofFn_succ, List.prod_cons]; rw [cm, ih]
  let u' : Fin n → (epsR S ⟶ G') := fun i =>
    Over.homMk (Geo.Tor.spMap (epsScaleR (f (c i))) ≫ (v' i).left)
      (by rw [Category.assoc, Over.w (v' i)]; exact hs _)
  have e2 : (fun i => d ≫ u i) = fun i => pushPt h.1.w (u' i) := by
    funext i
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, d, Over.homMk_left, pushPt, u', hu i, Category.assoc, hv i]
    rw [← Category.assoc, hcomm i, Category.assoc]
  refine ⟨u', fun i => rfl, ?_⟩
  apply inj_over h
  rw [hw, prod_push h u']
  show (d ≫ (List.ofFn u).prod).left = _
  rw [key, e2]

omit h in
theorem comb_iff_coord {n d : ℕ} {y : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G'} (hy : IsUnivChart G' n y) (c : Fin d → S)
    {v : Fin d → (epsR S ⟶ G')} (hv : ∀ i, IsTan (v i)) {w : epsR S ⟶ G'} (hw : IsTan w) :
    IsLieComb c v w ↔ tcoord hy w hw = ∑ i, c i • tcoord hy (v i) (hv i) := by
  obtain ⟨k, e⟩ := prodPts_tan hy c v hv
  rw [isLieComb_iff]
  exact ⟨fun q => (tcoord_congr hy q hw k).trans e, fun q => tan_ext hy hw k (q.trans e.symm)⟩

omit h in
theorem eq_of_comb_single [IsLocalRing S] [Smooth G'.hom] {d : ℕ} {v : Fin d → (epsR S ⟶ G')} (hv : ∀ i, IsTangent (v i))
    {w : epsR S ⟶ G'} (hw : IsTangent w) (j : Fin d) (hc : IsLieComb (Pi.single j 1) v w) : w = v j := by
  obtain ⟨u, hu, rfl⟩ := hc
  have oneL : ∀ {Y : Scheme.{0}} (T H : Over Y) [GrpObj H], (1 : T ⟶ H).left = T.hom ≫ η[H].left := by
    intro Y T H _
    show (toUnit T ≫ η[H]).left = _
    rw [Over.comp_left]
    congr 1
    all_goals first
      | simpa using Over.w (toUnit T)
      | (have e := Over.w (toUnit T)
         rwa [show (𝟙_ (Over Y)).hom = 𝟙 Y from rfl, Category.comp_id] at e)
  have single : ∀ {m : ℕ} (a : Fin m → (epsR S ⟶ G')) (k : Fin m), (∀ i, i ≠ k → a i = 1) →
      (List.ofFn a).prod = a k := by
    intro m
    induction m with
    | zero => intro a k; exact k.elim0
    | succ m ih =>
      intro a k ha
      rw [List.ofFn_succ, List.prod_cons]
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
      · have ht : (fun i : Fin m => a i.succ) = fun _ => 1 := funext fun i => ha _ (Fin.succ_ne_zero i)
        rw [ht]
        simp
      · rw [ha 0 (Fin.succ_ne_zero k').symm, _root_.one_mul]
        exact ih (fun i => a i.succ) k' (fun i hi => ha _ (fun e => hi (Fin.succ_injective _ e)))
  have hv' : ∀ i, Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (v i).left = η[G'].left := hv
  have h0 : Geo.Tor.spMap (epsScaleR (0 : S)) =
      (epsR S).hom ≫ Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
    simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
    congr 1
    all_goals (ext r <;> first
      | (simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]; done)
      | (simp [epsScaleR]; done))
  have h1 : Geo.Tor.spMap (epsScaleR (1 : S)) = 𝟙 _ := by
    simp only [Geo.Tor.spMap]
    rw [← Spec.map_id]
    congr 1
    all_goals (ext r <;> first
      | (simp [epsScaleR]; done)
      | (simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]; done))
  have hu1 : ∀ i, i ≠ j → u i = 1 := by
    intro i hi
    apply Over.OverMorphism.ext
    rw [hu i, Pi.single_eq_of_ne hi, h0, oneL, Category.assoc, hv' i]
  have huj : u j = v j := by
    apply Over.OverMorphism.ext
    rw [hu j, Pi.single_eq_same, h1, Category.id_comp]
  rw [single u j hu1, huj]

omit h in
theorem coords_basis [IsLocalRing S] [Smooth G'.hom] {d n : ℕ} {v : Fin d → (epsR S ⟶ G')} {u : Fin n → (epsR S ⟶ G')}
    (hv : IsLieBasis v) (hu : IsLieBasis u) (U : Fin n → Fin d → S) (hU : ∀ i, IsLieComb (U i) v (u i)) (z : Fin d → S) :
    ∃! a : Fin n → S, ∀ j, ∑ i, a i * U i j = z j := by
  obtain ⟨m, y, hy⟩ := univChartLoc G'
  have tv := fun i => (isTan_iff _).2 (hv.1 i)
  have tu := fun i => (isTan_iff _).2 (hu.1 i)
  obtain ⟨tw, -⟩ := prodPts_tan hy z v tv
  have hz : IsLieComb z v (prodPts z v) := (isLieComb_iff _ _ _).2 rfl
  have key : ∀ a : Fin n → S, IsLieComb a u (prodPts z v) ↔ ∀ j, ∑ i, a i * U i j = z j := fun a => by
    have e : ∑ i, a i • tcoord hy (u i) (tu i) = ∑ j, (∑ i, a i * U i j) • tcoord hy (v j) (tv j) := by
      simp only [(comb_iff_coord hy _ tv (tu _)).1 (hU _), Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    rw [comb_iff_coord hy a tu tw, e, ← comb_iff_coord hy _ tv tw, ← funext_iff]
    exact ⟨fun q => (hv.2 _ ((isTan_iff _).1 tw)).unique q hz, fun q => q ▸ hz⟩
  simpa only [key] using hu.2 _ ((isTan_iff _).1 tw)

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabMapCubical
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sabMap_cubical {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f : S' ⟶ S} (m₁ : SABMap t₁ t f)
    (m₂ : SABMap t₂ t f) (ψ : t₁.G ≅ t₂.G) [IsMonHom ψ.hom] (hφ : ψ.hom.left ≫ m₂.φ = m₁.φ) :
    (CubeMap.ofHom ψ.hom).IsPullCubical t₁.cub t₂.cub := by
  have hφ' : ψ.hom.left ≫ m₂.cm.F = m₁.cm.F := hφ
  have h3 : m₁.cm.F3 = (CubeMap.ofHom ψ.hom).F3 ≫ m₂.cm.F3 := hom_ext_triple _ fun i => by
    rw [cubeMap_comp_proj_three, Category.assoc, cubeMap_comp_proj_three]
    show _ = (ψ.hom ⊗ₘ ψ.hom ⊗ₘ ψ.hom).left ≫ _
    rw [← Category.assoc, ← Over.comp_left, ← cubeProj_comp_map, Over.comp_left, Category.assoc, hφ']
  exact pullCubCancel _ _ _ _ _ _ m₂.cm (CubeMap.ofHom ψ.hom) m₁.cm _ _ _ t.cub t₂.cub t₁.cub hφ'.symm h3
    (by show m₁.cm.e = 𝟙 _ ≫ m₂.cm.e; rw [Category.id_comp, m₁.base, m₂.base]) m₂.lin m₁.lin

theorem sabMap_iso {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f : S' ⟶ S} (m₁ : SABMap t₁ t f)
    (m₂ : SABMap t₂ t f) {L₁ : RigLB t₁.G} {L₂ : RigLB t₂.G} (h₁ : L₁ = t₁.PP) (h₂ : L₂ = t₂.PP) :
    ∃ ψ : t₁.G ≅ t₂.G, IsMonHom ψ.hom ∧ ψ.hom.left ≫ m₂.φ = m₁.φ ∧
      (∀ x, t₁.act.act x ≫ ψ.hom = ψ.hom ≫ t₂.act.act x) ∧
      ∃ (he : eSec t₁.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec t₂.G) (wL : LB.Iso L₁.L (L₂.L.pull ψ.hom.left)),
        wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec t₁.G) (fun _ => 1)) L₁.rig
          (rigPullOf ψ.hom.left (𝟙 _) he L₂.L L₂.rig) := by
  subst h₁ h₂
  obtain ⟨ψ, hψ, hφ⟩ := grpPullback_iso m₁.cart m₂.cart
  have hφ' : ψ.hom.left ≫ m₂.cm.F = m₁.cm.F := hφ
  refine ⟨ψ, hψ, hφ, fun x => ?_, ?_⟩
  · apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · simp only [Over.comp_left, Category.assoc, m₂.act, reassoc_of% hφ', hφ', m₁.act]
    · rw [Over.w, Over.w]
  · have := hψ
    obtain ⟨w, h₀, hg, hm⟩ := rigIso_congr rfl (CubeMap.ofHom ψ.hom) (sabMap_cubical m₁ m₂ ψ hφ) rfl rfl
    exact ⟨h₀, w, hg, hm⟩

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem ArcWit.uwIso {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b}
    {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X}
    (W W' : ArcWit Y a I f u χ) :
    ∃ ψ : W.t.G ≅ W'.t.G, ψ.hom.left ≫ W'.m.φ = W.m.φ ∧ IsMonHom ψ.hom ∧
      (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) ∧
      (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
        g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ →
        g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y.m.φ) ∧
      ∃ (he : eSec W.t.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec W'.t.G)
        (wL : LB.Iso W.P.U.LG.L (W'.P.U.LG.L.pull ψ.hom.left)),
        wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec W.t.G) (fun _ => 1)) W.P.U.LG.rig
          (rigPullOf ψ.hom.left (𝟙 _) he W'.P.U.LG.L W'.P.U.LG.rig) := by
  obtain ⟨ψ, hmon, hφ, hact, he, wL, hgen, hmaps⟩ :=
    sabMap_iso W.m W'.m (L₁ := W.P.U.LG) (L₂ := W'.P.U.LG) W.P.bundle W'.P.bundle
  refine ⟨ψ, hφ, hmon, hact, fun T g g₁ g₂ h1 h2 h3 => ?_, he, wL, hgen, hmaps⟩
  rw [hφ, h1]

  have hc := Y.m0.toSABMap.cart
  unfold IsGrpPullback at hc
  unfold SABMap.φ at h2
  rw [hc.1.hom_ext h2 h3]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TanSRestrict
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

def TanS {A : Type} [CommRing A] [Algebra S A] (y : sp (R₀ := S) (DualNumber A) ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom S A A) ≫ y = 1

theorem tanS_restrict {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (j : A →ₐ[S] A')
    {y : sp (R₀ := S) (DualNumber A) ⟶ G} (hy : TanS y) : TanS (spMap (dualMapS j) ≫ y) := by
  unfold TanS at hy ⊢
  rw [← Category.assoc, spMap_comp]
  have e : (TrivSqZeroExt.fstHom S A' A').comp (dualMapS j) = j.comp (TrivSqZeroExt.fstHom S A A) := by
    refine AlgHom.ext fun x => ?_
    simp [dualMapS_fst]
  rw [e, ← spMap_comp, Category.assoc, hy, comp_one'']

theorem tanS_scale {A : Type} [CommRing A] [Algebra S A] (c : A) {y : sp (R₀ := S) (DualNumber A) ⟶ G}
    (hy : TanS y) : TanS (spMap (scaleS c) ≫ y) := by
  unfold TanS at hy ⊢
  rw [← Category.assoc, spMap_comp]
  have e : (TrivSqZeroExt.fstHom S A A).comp (scaleS c) = TrivSqZeroExt.fstHom S A A := by
    refine AlgHom.ext fun x => ?_
    simp [scaleS_fst]
  rw [e, hy]

theorem fst_restrict (s : S) (A : Type) [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A]
    [IsScalarTower S (Localization.Away s) A] :
    (TrivSqZeroExt.fstHom (Localization.Away s) A A).restrictScalars S = TrivSqZeroExt.fstHom S A A := rfl

section Chart

variable {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A]
  [IsScalarTower S (Localization.Away s) A]

abbrev epsA (A : Type) [CommRing A] [Algebra (Localization.Away s) A] :
    Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] A :=
  (Algebra.ofId (Localization.Away s) A).comp (eps C)

theorem tanS_chart {y : sp (R₀ := S) (DualNumber A) ⟶ G} (hy : TanS y) :
    ∃ h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A, IsTanAt (epsA C A) h ∧ y = pushR G (pt C h) := by
  have hy' : pushR G (pullR (G := G) (R' := Localization.Away s) y) = y :=
    pushR_pullR (G := G) (R' := Localization.Away s) y
  have h0 : spMap (TrivSqZeroExt.fstHom (Localization.Away s) A A) ≫
      pullR (G := G) (R' := Localization.Away s) y = pt C (epsA C A) := by
    apply pushR_inj (G := G)
    rw [pushR_spMap, fst_restrict, hy', hy]
    simp only [epsA]
    rw [pt_eps, pushR_one]
  have hnil : ∀ a ∈ RingHom.ker (TrivSqZeroExt.fstHom (Localization.Away s) A A), IsNilpotent a := by
    intro a ha
    have h1 : a.fst = 0 := ha
    refine ⟨2, ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [pow_two, h1]
  have hcov := le_preimage_of_nil C (TrivSqZeroExt.fstHom (Localization.Away s) A A)
    (fun a => ⟨TrivSqZeroExt.inl a, by simp⟩) hnil _ (epsA C A) h0
  obtain ⟨h, hh⟩ := exists_pt C _ hcov
  refine ⟨h, ?_, ?_⟩
  · have h1 : pt C ((TrivSqZeroExt.fstHom (Localization.Away s) A A).comp h) = pt C (epsA C A) := by
      rw [← spMap_pt, ← hh, h0]
    have h2 := pt_injective C h1
    intro b
    simpa using AlgHom.congr_fun h2 b
  · rw [← hy', hh]

theorem chart_tanS (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) (hh : IsTanAt (epsA C A) h) :
    TanS (pushR G (pt C h)) := by
  unfold TanS
  rw [← fst_restrict s A, ← pushR_spMap, spMap_pt]
  have e : (TrivSqZeroExt.fstHom (Localization.Away s) A A).comp h = epsA C A := by
    refine AlgHom.ext fun b => ?_
    simpa using hh b
  rw [e]
  simp only [epsA]
  rw [pt_eps, pushR_one]

theorem chart_inj {h₁ h₂ : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A}
    (e : pushR G (pt C h₁) = pushR G (pt C h₂)) : h₁ = h₂ :=
  pt_injective C (pushR_inj (G := G) e)

theorem chart_map {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A']
    [IsScalarTower S (Localization.Away s) A'] (j : A →ₐ[Localization.Away s] A')
    (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) :
    spMap (dualMapS (j.restrictScalars S)) ≫ pushR G (pt C h) = pushR G (pt C ((dualMapS j).comp h)) := by
  rw [← spMap_pt, pushR_spMap]
  congr 2

theorem chart_scale (c : A) (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) :
    spMap (scaleS (S := S) c) ≫ pushR G (pt C h) = pushR G (pt C ((scaleS c).comp h)) := by
  rw [← spMap_pt, pushR_spMap]
  congr 2

def upS {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A']
    [IsScalarTower S (Localization.Away s) A'] (j : A →ₐ[S] A') : A →ₐ[Localization.Away s] A' :=
  { j with
    commutes' := fun r => by
      have : (j : A →+* A').comp (algebraMap (Localization.Away s) A) = algebraMap (Localization.Away s) A' :=
        IsLocalization.ringHom_ext (Submonoid.powers s) (by
          ext a
          simp [← IsScalarTower.algebraMap_apply])
      exact RingHom.congr_fun this r }

end Chart

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

