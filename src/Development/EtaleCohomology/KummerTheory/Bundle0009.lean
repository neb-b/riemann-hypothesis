module

public import Development.EtaleCohomology.KummerTheory.Bundle0002
public import Development.EtaleCohomology.KummerTheory.FinalTheorems
public import Development.EtaleCohomology.KummerTheory.Bundle0003

@[expose] public section

-- bundled from Development.EtaleCohomology.KummerTheory.LimOfIso
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.AffPf
open LateralTheory.KummerTheory.ContCut

theorem lim_of_iso {J : Type} [SmallCategory J] {K : Type 1} [Category.{0} K] {G G' : K ⥤ AddCommGrpCat.{1}}
    (e : G ≅ G') {D : J ⥤ K} (c : Cocone D) (h : Lim G c) : Lim G' c := by
  have nat : ∀ {a b : K} (f : a ⟶ b) (z : G.obj a), (G'.map f).hom ((e.hom.app a).hom z) = (e.hom.app b).hom ((G.map f).hom z) := by
    intro a b f z
    have := congrArg (fun φ => φ.hom z) (e.hom.naturality f)
    simpa using this.symm
  have inv : ∀ (a : K) (z : G'.obj a), (e.hom.app a).hom ((e.inv.app a).hom z) = z := by
    intro a z
    have := congrArg (fun φ => φ.hom z) (e.inv_hom_id_app a)
    simpa using this
  have inv' : ∀ (a : K) (z : G.obj a), (e.inv.app a).hom ((e.hom.app a).hom z) = z := by
    intro a z
    have := congrArg (fun φ => φ.hom z) (e.hom_inv_id_app a)
    simpa using this
  have natc : ∀ (j : J) (z : G.obj (D.obj j)), (G'.map (c.ι.app j)).hom ((e.hom.app (D.obj j)).hom z) =
      (e.hom.app c.pt).hom ((G.map (c.ι.app j)).hom z) := fun j z => nat (c.ι.app j) z
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := h.1 ((e.inv.app c.pt).hom x)
    refine ⟨j, (e.hom.app (D.obj j)).hom y, ?_⟩
    rw [natc, hy, inv]
  · have h0 : (G.map (c.ι.app j)).hom ((e.inv.app (D.obj j)).hom y) = 0 := by
      have h1 := natc j ((e.inv.app (D.obj j)).hom y)
      rw [inv, hy] at h1
      have h2 := congrArg (e.inv.app c.pt).hom h1
      rw [inv', map_zero] at h2
      exact h2.symm
    obtain ⟨k, f, hf⟩ := h.2 j _ h0
    refine ⟨k, f, ?_⟩
    have h1 := nat (D.map f) ((e.inv.app (D.obj j)).hom y)
    rw [inv, hf, map_zero] at h1
    exact h1

theorem Aff_of (hR : AffRing) : Aff := by
  intro hb q X _ R p hq J _ _ D c hc n i
  obtain ⟨T, ⟨e⟩, hmap, hcol⟩ := hR p
  obtain ⟨hT⟩ := hcol c hc
  have unit : ∀ A, IsUnit ((q : ℕ) : T.obj A) := by
    intro A
    obtain ⟨φ⟩ := hmap A
    simpa using hq.map φ.hom
  have key : Lim (T ⋙ Scheme.Spec.rightOp ⋙ Hf (tw q i) n) c := by
    have hB := hb q (D ⋙ T) (T.mapCocone c) hT n i
    refine ⟨fun x => ?_, fun j y hy => ?_⟩
    · obtain ⟨j, y, hy⟩ := hB.1 x (unit c.pt)
      exact ⟨j, y, hy⟩
    · obtain ⟨k, f, hf⟩ := hB.2 j y (unit (D.obj j)) hy
      exact ⟨k, f, hf⟩
  exact lim_of_iso (Functor.isoWhiskerRight e (Hf (tw q i) n)).symm c key

end LateralTheory.KummerTheory.AffPf

end
end

-- bundled from Development.EtaleCohomology.KummerTheory.LocCokPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

def AffNbhd : Prop := ∀ {R : CommRingCat.{0}} (U : Over (Spec R)) (u : U.left),
  ∃ (B : CommRingCat.{0}) (s : R ⟶ B) (ι : Spec B ⟶ U.left) (_ : IsOpenImmersion ι) (b : Spec B),
    ι ≫ U.hom = Spec.map s ∧ ι b = u

def CokAff : Prop := A2 → DivisorNaturality → B1 → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
  [QuasiCompact p] [IsSeparated p], IsUnit (q : R) →
  ∀ (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ) (n : ℤ),
  (∀ (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsoUpTo N (lh q p (Spec.map s) i r c M n)) →
  ∀ (B : CommRingCat.{0}) (s : R ⟶ B) (b : Spec B) (x : Ht q (sch.obj (pullback p (Spec.map s))) n i),
  ∃ (C : CommRingCat.{0}) (t : B ⟶ C), t.hom.Etale ∧ (∃ w : Spec C, Spec.map t w = b) ∧
    ∃ y, lh q p (Spec.map (s ≫ t)) i r c M n y = N • pull _ (sch.map (bcMap p s (s ≫ t) t rfl)) _ _ x

theorem affNbhd : AffNbhd := by
  intro R U u
  obtain ⟨b, hb⟩ := U.left.affineCover.covers u
  exact ⟨_, Spec.preimage (U.left.affineCover.f (U.left.affineCover.idx u) ≫ U.hom),
    U.left.affineCover.f (U.left.affineCover.idx u), U.left.affineCover.map_prop _, b, by simp, hb⟩

theorem locCok_of (hA : AffNbhd) (hC : CokAff) : LocCok := by
  intro h2 h6 hb1 q _ X R p _ _ hq i r c M N n hiso U u x
  obtain ⟨B, s, ι, _, b, hs, hb'⟩ := hA U u
  let g0 : Over.mk (Spec.map s) ⟶ U := Over.homMk ι hs
  obtain ⟨C, t, ht, ⟨w, hw⟩, y, hy⟩ := hC h2 h6 hb1 q p hq i r c M N n hiso B s b
    (pull _ (sch.map (rst p g0)) _ _ x)
  have : Etale (Spec.map t) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 ht
  let g : Over.mk (Spec.map (s ≫ t)) ⟶ U := Over.homMk (Spec.map t ≫ ι) (by simp [hs, Spec.map_comp])
  refine ⟨Over.mk (Spec.map (s ≫ t)), g, ⟨?_, w, ?_⟩, y, ?_⟩
  · show Etale (Spec.map t ≫ ι); infer_instance
  · show (Spec.map t ≫ ι) w = u
    rw [Scheme.Hom.comp_apply, hw, hb']
  · show lh q p (Spec.map (s ≫ t)) i r c M n y = _
    have key : bcMap p s (s ≫ t) t rfl ≫ rst p g0 = rst p g := by
      apply pullback.hom_ext
      · simp only [bcMap, rst, g, g0, pullback.map, Over.homMk_left, Category.assoc, Category.comp_id]
        erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
        rfl
      · simp only [bcMap, rst, g, g0, pullback.map, Over.homMk_left, Category.assoc, Category.comp_id]
        erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]
        simp only [Category.assoc]
        rfl
    rw [hy, ← pull_comp, ← Functor.map_comp, key]

theorem locCok_of_cokAff (hC : CokAff) : LocCok := locCok_of affNbhd hC

end LateralTheory.KummerTheory.LHCut
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.LocKerPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

lemma lk_aff (X : Scheme.{0}) (x : X) :
    ∃ (B : CommRingCat.{0}) (f : Spec B ⟶ X), IsOpenImmersion f ∧ x ∈ Set.range f :=
  by
  let 𝒰 := X.affineCover
  have h2 : IsOpenImmersion (𝒰.f (𝒰.idx x)) := inferInstance
  exact ⟨_, 𝒰.f (𝒰.idx x), h2, 𝒰.covers x⟩

lemma lk_etale {A B : CommRingCat.{0}} (f : A ⟶ B) (h : f.hom.Etale) : Etale (Spec.map f) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr h

lemma lk_fin {J : Type} [SmallCategory J] [IsFiltered J] (j₀ : J) {ι : Type} [Finite ι]
    (P : ι → ∀ {k : J}, (j₀ ⟶ k) → Prop)
    (hP : ∀ t {k k' : J} (f : j₀ ⟶ k) (g : k ⟶ k'), P t f → P t (f ≫ g))
    (h : ∀ t, ∃ (k : J) (f : j₀ ⟶ k), P t f) : ∃ (k : J) (f : j₀ ⟶ k), ∀ t, P t f := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, ∃ (k : J) (f : j₀ ⟶ k), ∀ t ∈ s, P t f by
    obtain ⟨k, f, hf⟩ := H Finset.univ
    exact ⟨k, f, fun t => hf t (Finset.mem_univ t)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨j₀, 𝟙 _, by simp⟩
  | insert a s _ ih =>
    obtain ⟨k, f, hf⟩ := ih
    obtain ⟨k', f', hf'⟩ := h a
    obtain ⟨k'', g, g', hg⟩ := IsFiltered.span f f'
    refine ⟨k'', f ≫ g, fun t ht => ?_⟩
    rcases Finset.mem_insert.1 ht with rfl | ht
    · rw [hg]; exact hP _ _ _ hf'
    · exact hP _ _ _ (hf t ht)

lemma lk_pull_spMap {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) {n i : ℤ} {q : ℕ} (x : Ht q (sp A) n i) :
    pull _ (spMap (f ≫ g).hom) _ _ x = pull _ (spMap g.hom) _ _ (pull _ (spMap f.hom) _ _ x) := by
  simp only [spMap, CommRingCat.ofHom_hom]
  rw [Spec.map_comp, Functor.map_comp, pull_comp]

theorem locKer_of (hS : StrictHenselization) (hL : LhNat) : LocKer := by
  intro hA hB q _ X R p hq i r c M N n hiso U u y hy
  obtain ⟨B, ι, hι, b, hb⟩ := lk_aff U.left u
  obtain ⟨J, _, _, D, cc, hc, w, hSH, hw⟩ := hS B b
  obtain ⟨j₀⟩ := IsFiltered.nonempty (C := J)
  let φ : Spec cc.pt ⟶ U.left := Spec.map (w.app j₀ ≫ cc.ι.app j₀) ≫ ι
  let V' : Over (Spec R) := Over.mk (Spec.map (Spec.preimage (φ ≫ U.hom)))
  let g' : V' ⟶ U := Over.homMk φ (Spec.map_preimage (φ ≫ U.hom)).symm
  have h1 := hL hA q p i r c M n g' y
  rw [hy, map_zero] at h1
  have h2 := (hiso cc.pt (Spec.preimage (φ ≫ U.hom)) hSH).1 _ h1.symm
  let ψ : Spec (D.obj j₀) ⟶ U.left := Spec.map (w.app j₀) ≫ ι
  have hunit : ∀ j, IsUnit ((q : ℕ) : D.obj j) := by
    intro j
    have := hq.map (Spec.preimage (Spec.map (w.app j) ≫ ι ≫ U.hom)).hom
    simpa using this
  let z : ∀ t : (Σ a : Fin (M + 1), Fin (r a)), Ht q (sp (D.obj j₀)) (n - ((t.1 : ℕ) : ℤ)) 0 :=
    fun t => N • pull _ (sch.map ψ) _ _ (y t.1 t.2)
  have e1 : spMap (cc.ι.app j₀).hom ≫ sch.map ψ = sch.map φ := by
    simp only [spMap, CommRingCat.ofHom_hom, ψ, φ, ← Functor.map_comp, Spec.map_comp, Category.assoc]
  have hz : ∀ t, pull _ (spMap (cc.ι.app j₀).hom) _ _ (z t) = 0 := by
    intro t
    have := congrFun (congrFun h2 t.1) t.2
    simp only [Pi.smul_apply] at this
    simp only [z, map_nsmul]
    rw [← pull_comp, e1]
    exact this
  have hk : ∀ t, ∃ (k : J) (f : j₀ ⟶ k), pull _ (spMap (D.map f).hom) _ _ (z t) = 0 := fun t =>
    (hB q D cc hc _ _).2 j₀ (z t) (hunit j₀) (hz t)
  obtain ⟨k, F, hF⟩ := lk_fin j₀ (fun t {k} (f : j₀ ⟶ k) => pull _ (spMap (D.map f).hom) _ _ (z t) = 0)
    (fun t k k' f g hf => by simp only [Functor.map_comp, lk_pull_spMap, hf, map_zero]) hk
  let gl : Spec (D.obj k) ⟶ U.left := Spec.map (w.app k) ≫ ι
  have hwk : w.app k = w.app j₀ ≫ D.map F := by simpa using (w.naturality F)
  have := lk_etale _ (hw k).1
  obtain ⟨𝔮, h𝔮⟩ := (hw k).2
  refine ⟨Over.mk (gl ≫ U.hom), Over.homMk gl rfl, ⟨?_, 𝔮, ?_⟩, fun a s => ?_⟩
  · change Etale gl; infer_instance
  · change ι (Spec.map (w.app k) 𝔮) = u
    rw [← hb]; congr 1; exact PrimeSpectrum.ext h𝔮
  · have := hF ⟨a, s⟩
    have e2 : sch.map gl = spMap (D.map F).hom ≫ sch.map ψ := by
      simp only [gl, ψ, hwk, spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Functor.map_comp]
    change N • pull _ (sch.map gl) _ _ (y a s) = 0
    rw [e2, pull_comp, ← map_nsmul]
    exact this

end LateralTheory.KummerTheory.LHCut
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.MVnatPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.MVnatPf

open LateralTheory.KummerTheory.ContCut

theorem res_res {R : Type} [CommRing R] {F : Shv R} {A B C : Scheme.{0}} (g₁ : A ⟶ B) (g₂ : B ⟶ C) (x : Sec F C) :
    Sec.res g₁ (Sec.res g₂ x) = Sec.res (g₁ ≫ g₂) x := by
  show _ = (F.obj.map (g₁ ≫ g₂).op).hom x
  rw [op_comp, Functor.map_comp]
  rfl

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {A B : Scheme.{0}} (g : A ⟶ B) (x : Sec F B) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show ((F.obj.map g.op) ≫ φ.hom.app (op A)).hom x = (φ.hom.app (op B) ≫ G.obj.map g.op).hom x
  rw [φ.hom.naturality]

theorem conn_pull (hD : Dict) {R : Type} [CommRing R] (F : Shv R) {W U V X W' U' V' X' : Scheme.{0}}
    (a : W ⟶ U) (f : U ⟶ X) (g : V ⟶ X) (a' : W' ⟶ U') (f' : U' ⟶ X') (g' : V' ⟶ X')
    (hw : W' ⟶ W) (hu : U' ⟶ U) (hv : V' ⟶ V) (hx : X' ⟶ X)
    (ea : a' ≫ hu = hw ≫ a) (ef : f' ≫ hx = hu ≫ f) (eg : g' ≫ hx = hv ≫ g) (n : ℤ) w x
    (h : Conn F a f g n w x) :
    Conn F a' f' g' n (pull R (sch.map hw) F n w) (pull R (sch.map hx) F (n + 1) x) := by
  obtain ⟨s, z, hs, hz, e1, e2⟩ := h
  refine ⟨Sec.res hu s, Sec.res hx z, ?_, ?_, ?_, ?_⟩
  · have := (hD R (res R F) W n).2.2.2.2 hw w _ hs
    rw [res_res, ea, ← res_res]
    exact this
  · exact (hD R (res R F) X (n + 1)).2.2.2.2 hx x _ hz
  · rw [res_res, ef, ← res_res, e1, map_res]
  · rw [res_res, eg, ← res_res, e2]
    exact map_zero _

theorem unop_nat {K : Type 1} [Category.{0} K] {A B : K ⥤ Scheme.{0}ᵒᵖ} (φ : A ⟶ B) {k k' : K} (h : k ⟶ k') :
    (φ.app k').unop ≫ (A.map h).unop = (B.map h).unop ≫ (φ.app k).unop := by
  have := congrArg Quiver.Hom.unop (φ.naturality h)
  rw [unop_comp, unop_comp] at this
  exact this

theorem MVnat_of (hD : Dict) (hΔ : Delta) (hE : Exact) : MVnat := by
  intro R _ F K _ X U V W f g a b hM
  have dk : ∀ (n : ℤ) (k : K), ∃ δ : H R (sch.obj (W.obj k).unop) F n →+ H R (sch.obj (X.obj k).unop) F (n + 1),
      ∀ w x, Conn F (a.app k).unop (f.app k).unop (g.app k).unop n w x ↔ δ w = x :=
    fun n k => hΔ R F _ _ _ _ (hM k) n
  choose δ hδ using dk
  refine ⟨{
    f := fun n => Functor.whiskerRight f (Hf F n)
    g := fun n => Functor.whiskerRight g (Hf F n)
    a := fun n => Functor.whiskerRight a (Hf F n)
    b := fun n => Functor.whiskerRight b (Hf F n)
    δ := fun n =>
      { app := fun k => AddCommGrpCat.ofHom (δ n k)
        naturality := fun k k' h => by
          apply AddCommGrpCat.hom_ext
          ext w
          show δ n k' (pull R (sch.map (W.map h).unop) F n w) = pull R (sch.map (X.map h).unop) F (n + 1) (δ n k w)
          exact (hδ n k' _ _).1 (conn_pull hD F _ _ _ _ _ _ _ _ _ _ (unop_nat a h) (unop_nat f h) (unop_nat g h) n _ _
            ((hδ n k _ _).2 rfl)) }
    comm := fun n => by
      ext k : 2
      simp only [NatTrans.comp_app, Functor.whiskerRight_app]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply Quiver.Hom.unop_inj
      rw [unop_comp, unop_comp]
      exact (hM k).2.2.1.w
    exUV := fun n k u v h => (hE R F _ _ _ _ (hM k) n).1 u v h
    exX := fun n k x h1 h2 => by
      obtain ⟨w, hw⟩ := (hE R F _ _ _ _ (hM k) n).2.1 x h1 h2
      exact ⟨w, (hδ n k w x).1 hw⟩
    exW := fun n k w => (hδ n k w 0).symm.trans ((hE R F _ _ _ _ (hM k) n).2.2 w) }⟩

end LateralTheory.KummerTheory.MVnatPf

end
end

-- bundled from Development.EtaleCohomology.KummerTheory.PlaceExPf
section
noncomputable section

namespace LateralTheory.KummerTheory

def PlaceGood (k K : Type) [Field k] [Field K] [Algebra k K] (A : LocalSubring K) : Prop :=
  (∀ c : k, algebraMap k K c ∈ A.toSubring) ∧
    ∀ a ∈ A.toSubring, ∃ c : k, a = algebraMap k K c ∨ (a - algebraMap k K c)⁻¹ ∉ A.toSubring

def PlaceZorn : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K],
  ∃ A : LocalSubring K, PlaceGood k K A ∧ ∀ B : LocalSubring K, A ≤ B → PlaceGood k K B → B ≤ A

def PlaceStep : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] (A : LocalSubring K),
  PlaceGood k K A → (∀ B : LocalSubring K, A ≤ B → PlaceGood k K B → B ≤ A) →
    ∀ x : K, x ∈ A.toSubring ∨ x⁻¹ ∈ A.toSubring

theorem PlaceEx_of (h1 : PlaceZorn) (h2 : PlaceStep) : PlaceEx := by
  intro k K _ _ _ _ _
  obtain ⟨A, hA, hmax⟩ := h1 k K
  have hv := h2 k K A hA hmax
  let T : ValuationSubring K := ⟨A.toSubring, hv⟩
  let σ : k →+* T := (algebraMap k K).codRestrict T (fun c => hA.1 c)
  refine ⟨T, σ, fun x => rfl, ?_⟩
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := hA.2 a a.2
  refine ⟨c, ?_⟩
  simp only [RingHom.comp_apply]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
  have hK : ((σ c : K) - (a : K)) * (w : K) = 1 := by
    have := congrArg (fun z : T => (z : K)) hw
    simpa using this
  rcases hc with h | h
  · have : (σ c : K) - (a : K) = 0 := by rw [h]; simp [σ]
    rw [this, zero_mul] at hK; exact zero_ne_one hK
  · apply h
    have hinv : ((σ c : K) - (a : K))⁻¹ = (w : K) := inv_eq_of_mul_eq_one_right hK
    have : ((a : K) - algebraMap k K c)⁻¹ = -(w : K) := by
      rw [← hinv, ← inv_neg, neg_sub]; rfl
    rw [this]; exact T.neg_mem _ w.2

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.PlacePfVal
section
noncomputable section
open GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory.ValAICPf

variable {K : Type} [Field K] [IsAlgClosed K] (T : ValuationSubring K)

theorem mem_of_root (p : T[X]) (hp : p.Monic) (r : K) (hr : (p.map (algebraMap T K)).eval r = 0) : r ∈ T := by
  have hi : IsIntegral T r := ⟨p, hp, by rwa [eval_map] at hr⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := T) (K := K)).mp hi
  rw [← hy]; exact y.2

theorem aic : AIC T := by
  intro p hp hd
  have hd' : (p.map (algebraMap T K)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective (IsFractionRing.injective T K)]
    intro h; rw [degree_eq_natDegree hp.ne_zero] at h; norm_cast at h; omega
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hd'
  have hrT := mem_of_root T p hp r hr
  refine ⟨⟨r, hrT⟩, ?_⟩
  apply IsFractionRing.injective T K
  rw [map_zero, ← eval₂_hom, ← eval_map]
  exact hr

theorem prod_lt (s : Multiset K) (hs : ∀ r ∈ s, T.valuation r ≤ 1) (h : T.valuation s.prod < 1) :
    ∃ r ∈ s, T.valuation r < 1 := by
  by_contra hc
  push_neg at hc
  have : T.valuation s.prod = 1 := by
    rw [map_multiset_prod]
    apply Multiset.prod_eq_one
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    exact le_antisymm (hs r hr) (hc r hr)
  rw [this] at h; exact lt_irrefl _ h

theorem hens : HenselianLocalRing T where
  is_henselian := by
    intro f hf a₀ h₁ _
    set q := f.map (algebraMap T K)
    have he : (algebraMap T K) (f.eval a₀) = (q.roots.map (fun r => (a₀ : K) - r)).prod := by
      rw [← eval₂_hom, ← eval_map]
      exact (IsAlgClosed.splits q).eval_eq_prod_roots_of_monic (hf.map _) _
    have hmem : ∀ r ∈ q.roots, r ∈ T := fun r hr =>
      mem_of_root T f hf r ((mem_roots (hf.map _).ne_zero).mp hr)
    have hlt : T.valuation (q.roots.map (fun r => (a₀ : K) - r)).prod < 1 := by
      rw [← he]; exact (T.valuation_lt_one_iff _).mp h₁
    obtain ⟨x, hx, hxv⟩ := prod_lt T _ (by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
      exact (T.valuation_le_one_iff _).mpr (T.sub_mem a₀.2 (hmem r hr))) hlt
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    refine ⟨⟨r, hmem r hr⟩, ?_, ?_⟩
    · have h0 := (mem_roots (hf.map _).ne_zero).mp hr
      apply IsFractionRing.injective T K
      rw [map_zero, ← eval₂_hom, ← eval_map]
      exact h0
    · rw [T.valuation_lt_one_iff]
      have hc : (((⟨r, hmem r hr⟩ : T) - a₀ : T) : K) = -((a₀ : K) - r) := by push_cast; ring
      rw [hc, Valuation.map_neg]
      exact hxv

end LateralTheory.KummerTheory.ValAICPf

theorem LateralTheory.KummerTheory.ValAIC_of : LateralTheory.KummerTheory.ValAIC := fun K _ _ T => ⟨LateralTheory.KummerTheory.ValAICPf.aic T, LateralTheory.KummerTheory.ValAICPf.hens T⟩

theorem LateralTheory.KummerTheory.Place_of_ex (h : LateralTheory.KummerTheory.PlaceEx) : LateralTheory.KummerTheory.Place :=
  LateralTheory.KummerTheory.Place_of h LateralTheory.KummerTheory.ValAIC_of
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.RedEpiPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedEpiPf
open LateralTheory.KummerTheory.BockCut

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (y : Sec F U) : Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

theorem sec_TZ_eq_zero {q : ℕ} (hq : q = 1) (i : ℤ) {V : Scheme.{0}} (x : Sec (TZ q i) V) : x = 0 := by
  subst hq
  have : Subsingleton (Sec (tw 1 i) V) := Module.subsingleton (ULift.{1} (ZMod 1)) _
  exact Subsingleton.elim (α := Sec (tw 1 i) V) x 0

theorem RedEpi_of (h_tw : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (h_pb : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities)
    (h_pl : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (h_me : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria)
    (h_lb : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) : LateralTheory.KummerTheory.BockCut.RedEpi := by
  intro l _ c a hac i π hπ
  obtain ⟨hall, hmono, -, -, htrans, -, -⟩ := h_lb
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ a) := ⟨pow_ne_zero _ hl0⟩
  have : NeZero (l ^ c) := ⟨pow_ne_zero _ hl0⟩
  refine ((h_me ℤ π).2.2.1).2 ?_
  intro U y
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · apply hall
    intro V g
    exact ⟨0, (sec_TZ_eq_zero (pow_zero l) i _).trans (sec_TZ_eq_zero (pow_zero l) i _).symm⟩
  · suffices key : ∀ y' : Sec (tw (l ^ a) i) U, Loc U fun V g =>
        ∃ x : Sec (TZ (l ^ c) i) V, Sec.map π x = (Sec.res (F := tw (l ^ a) i) g y' : Sec (tw (l ^ a) i) V) from key y
    clear y
    intro y
    apply htrans
    refine hmono _ _ _ ((h_tw (l ^ a) i).1 U y) ?_
    intro V g hd
    rcases hd with h0 | ⟨ξ, d, hξ⟩
    · apply hall
      intro W k
      refine ⟨0, ?_⟩
      have e1 : Sec.res (F := tw (l ^ a) i) (k ≫ g) y = 0 := by
        rw [res_comp, h0]
        exact map_zero ((tw (l ^ a) i).obj.map k.op).hom
      have e2 : Sec.map π (0 : Sec (TZ (l ^ c) i) W) = 0 := map_zero (π.hom.app (op W)).hom
      exact e2.trans e1.symm
    · have hla : IsUnit ((l : Γ(V, ⊤)) ^ a) := by simpa using ξ.2.1
      have hl : IsUnit (l : Γ(V, ⊤)) := (isUnit_pow_iff ha.ne').1 hla
      have hlc : IsUnit ((l ^ c : ℕ) : Γ(V, ⊤)) := by simpa using hl.pow c
      apply htrans
      refine hmono _ _ _ ((h_pl (l ^ c) V).1 hlc) ?_
      rintro W k ⟨ζ⟩
      obtain ⟨ζ', hζ'⟩ := (h_pb (l ^ c) Γ(W, ⊤)).2.2.2.2.2 (l ^ a) (pow_dvd_pow l hac) ζ
      refine hmono _ _ _ ((h_tw (l ^ a) i).2.1 W ζ' (Sec.res (F := tw (l ^ a) i) k (Sec.res (F := tw (l ^ a) i) g y))) ?_
      rintro W' k' ⟨e, he⟩
      beta_reduce
      refine ⟨e • genZ i (ζ.map k'.appTop.hom), ?_⟩
      have hr : (ζ'.map k'.appTop.hom).1 = (ζ.map k'.appTop.hom).1 ^ (l ^ c / l ^ a) := by
        show k'.appTop.hom ζ'.1 = (k'.appTop.hom ζ.1) ^ _
        rw [hζ', map_pow]
      have e3 : Sec.res (F := tw (l ^ a) i) ((k' ≫ k) ≫ g) y = e • twGen i (ζ'.map k'.appTop.hom) := by
        rw [res_comp, res_comp, he]
      have e4 : Sec.map π (e • genZ i (ζ.map k'.appTop.hom)) = e • genZ i (ζ'.map k'.appTop.hom) :=
        (map_nsmul (π.hom.app (op W')).hom e _).trans (congrArg (fun z => e • z) (hπ W' _ _ hr))
      exact e4.trans e3.symm

end LateralTheory.KummerTheory.RedEpiPf
end
end

