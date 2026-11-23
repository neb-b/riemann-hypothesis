module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.Bridge
open GlobalTheory.ConstFam GlobalTheory.FieldBaseChange

section General
variable {X X' X₁ X₂ Y Y' : Scheme.{0}}

theorem exists_iso_section {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (w₀ : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w₀.IsGen) (g : X₁ ⟶ Y) (hg : g ≫ f₁ = 𝟙 _) :
    ∃ w₁ : LB.Iso L₁ (L₂.pull (g ≫ f₂)), PGen w₁ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (i : L₁.ι),
      (g ≫ f₂) (r z) ∈ L₂.U j → r z ∈ L₁.U i → gw w₁ r z j i = GlobalTheory.BoxExpansion.pw w₀ (r ≫ g) z i j := by
  have hpt : ∀ x : X₁, f₁ (g x) = x := fun x => congrArg (fun q => q x) hg
  have le : ∀ (J : PUnit → L₂.ι) (i : L₁.ι), (L₂.pull (g ≫ f₂)).U J ⊓ L₁.U i ≤
      g ⁻¹ᵁ ((L₂.pull f₂).U J ⊓ (L₁.pull f₁).U (fun _ => i)) := fun J i x hx =>
    ⟨mem_pull.2 (mem_pull₂.1 hx.1), mem_pull.2 (by rw [hpt]; exact hx.2)⟩
  let w₁ : LB.Iso L₁ (L₂.pull (g ≫ f₂)) := ⟨fun p => res (le p.1 p.2) (pullU g _ (w₀.s (p.1, fun _ => p.2)))⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (i : L₁.ι),
      (g ≫ f₂) (r z) ∈ L₂.U j → r z ∈ L₁.U i → gw w₁ r z j i = GlobalTheory.BoxExpansion.pw w₀ (r ≫ g) z i j :=
    fun Z r z j i hj hi => by
      have hm : r z ∈ (L₂.pull (g ≫ f₂)).U (fun _ => j) ⊓ L₁.U i := ⟨mem_pull.2 hj, hi⟩
      exact (gm_res r z (le _ _) hm _).trans (gm_pull r g z _ (le _ _ hm) _)
  refine ⟨w₁, fun Z r z j j' i i' hj hj' hi hi' => ?_, key⟩
  have := GlobalTheory.BoxExpansion.pw_trans hw (r ≫ g) z (j₁ := i) (j₁' := i') (j₂ := j) (j₂' := j')
    (by show f₁ (g (r z)) ∈ _; rw [hpt]; exact hi) (by show f₁ (g (r z)) ∈ _; rw [hpt]; exact hi') hj hj'
  rw [Category.assoc, Category.assoc, hg, Category.comp_id] at this
  rw [key Z r z j i hj hi, key Z r z j' i' hj' hi', this]

variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}

theorem pmaps_of_val (hL : L.IsLB) (hL' : L'.IsLB) {φ' : PUnit → (Y' ⟶ X')} {φ : PUnit → (Y ⟶ X)} {ε : PUnit → ℤ}
    {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J J', Good L z J → Good L' z J' →
      val t (r ≫ h) z J = (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k) * val a r z J') : PMaps w φ' φ ε a t h := by
  intro Z r z p q hp hq
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun k => (r ≫ φ' k) ≫ F) p (fun _ _ _ => rfl) hp
  obtain ⟨J', hJ', e'⟩ := exists_good L' hL' z (fun k => r ≫ φ' k) q (fun _ _ _ => rfl) hq
  have := H Z r z J J' hJ hJ'
  rw [val_of t _ z J p (fun k => by rw [← e k, Category.assoc, Category.assoc, hψ]), val_of a _ z J' q e'] at this
  refine this.trans (congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_))
  rw [wVal, e k, e' k]

theorem exists_equiv (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (e : Y ≅ X') {R : Type} [CommRing R]
    (π' : X' ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ Spec (CommRingCat.of R)) (hπ : e.inv ≫ π = π') (p : Y ⟶ X)
    (hp : p = e.hom ≫ F) (k : ℤ) :
    ∃ θ : SecOver π (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k)) ≃ₗ[R]
        SecOver π' (LB.LinComb L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)),
      ∀ t (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) J J', Good L z J → Good L' z J' →
        sval t (r ≫ e.inv) z J = (wVal w z J J' r ^ k).val * sval (θ t) r z J' := by
  subst hp
  have hψ : ∀ _ : Fin 1, 𝟙 X' ≫ F = e.inv ≫ e.hom ≫ F := fun _ => by rw [e.inv_hom_id_assoc, Category.id_comp]
  have hid : e.inv ≫ π = π' ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, hπ]
  let θ := pullThrough (φ := fun _ : Fin 1 => e.hom ≫ F) (φ' := fun _ : Fin 1 => 𝟙 X') hw hL hL' hψ (fun _ => k) hid
  have hθ : ∀ t (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) J J', Good L z J → Good L' z J' →
      sval t (r ≫ e.inv) z J = (wVal w z J J' r ^ k).val * sval (θ t) r z J' := fun t Z r z J J' hJ hJ' => by
    have := sval_pullThrough (φ := fun _ : Fin 1 => e.hom ≫ F) (φ' := fun _ : Fin 1 => 𝟙 X') hw hL hL' hψ hid t r hJ hJ'
    rwa [Fin.prod_univ_one, Category.comp_id] at this
  refine ⟨LinearEquiv.ofBijective θ ⟨?_, fun a => ?_⟩, hθ⟩
  · refine (injective_iff_map_eq_zero θ).2 fun t ht => sec_ext' hL fun y J hJ => ?_
    obtain ⟨J', hJ'⟩ := exists_good' hL' y
    have := hθ t _ e.hom y J J' hJ hJ'
    rw [e.hom_inv_id, ht, sval_zero' hJ', mul_zero] at this
    rw [this, sval_zero' hJ]
  · have hq : e.hom ≫ π' = (e.hom ≫ π') ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
    have hφ : ∀ _ : Fin 1, e.hom = e.hom ≫ 𝟙 X' := fun _ => (Category.comp_id _).symm
    obtain ⟨t, ht⟩ := exists_sec_up (φ' := fun _ : Fin 1 => e.hom) ((isGen_iff w).1 hw) hL hL'
      (pullOver L' (fun _ => k) hq hφ a)
    have H : SecThrough w (fun _ : Fin 1 => e.hom) (fun _ => e.hom ≫ F) (fun _ => k)
        (pullOver L' (fun _ => k) hq hφ a) t (𝟙 _) := fun Z r z p q hp hq => by
      rw [Category.comp_id]
      exact ht Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
    refine ⟨t, sec_ext' hL' fun y J' hJ' => ?_⟩
    obtain ⟨J, hJ⟩ := exists_good' hL y
    have a₁ := H.sval (fun _ => (Category.id_comp _).symm) e.inv hJ hJ'
    have a₂ := hθ t _ (𝟙 _) y J J' hJ hJ'
    rw [Fin.prod_univ_one, sval_pullOver hq hφ a _ hJ', e.inv_hom_id, Category.comp_id] at a₁
    rw [Category.id_comp] at a₂
    exact (Units.mul_right_inj _).1 (a₂.symm.trans a₁)

end General

section Basis
variable {Z : Scheme.{0}} {G₀ : Over Z} {L₀ : LB G₀.left} {R : Type} [CommRing R]
  {G : Over (Spec (CommRingCat.of R))} {L : LB G.left} {χ : Sp R ⟶ Z} {Φ : G.left ⟶ G₀.left}

theorem exists_basis (hL₀ : L₀.IsLB) (hL : L.IsLB) (H : IsPullback Φ G.hom G₀.hom χ) {ω : LB.Iso L (L₀.pull Φ)}
    (hω : ω.IsGen) {k n : ℕ} (σ : Fin n → H0 L k) (hσ : IsBasisH σ) :
    ∃ (g : G.left ⟶ (Over.mk χ ⊗ G₀).left) (b : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk χ))),
      g ≫ (fst (Over.mk χ) G₀).left = G.hom ∧ g ≫ (snd (Over.mk χ) G₀).left = Φ ∧ BasisAlong G₀ L₀ k (𝟙 _) b ∧
      ∀ i (Y : Scheme.{0}) (r : Y ⟶ G.left) (z : Y) J J', Good L₀ z J → Good L z J' →
        sval (L := L₀) (φ := fun _ : Fin 1 => (snd (Over.mk χ) G₀).left) (ε := fun _ => (k : ℤ)) (b i) (r ≫ g) z J =
          (wVal ω z J J' r).val ^ k * sval (σ i) r z J' := by
  let e : G.left ≅ (Over.mk χ ⊗ G₀).left := H.flip.isoPullback
  have e₁ : e.hom ≫ (fst (Over.mk χ) G₀).left = G.hom := H.flip.isoPullback_hom_fst
  have e₂ : e.hom ≫ (snd (Over.mk χ) G₀).left = Φ := H.flip.isoPullback_hom_snd
  obtain ⟨θ, hθ⟩ := exists_equiv hω hL₀ hL e.symm G.hom (fst (Over.mk χ) G₀).left e₁ (snd (Over.mk χ) G₀).left
    (by rw [← e₂]; exact (e.inv_hom_id_assoc _).symm) (k : ℤ)
  refine ⟨e.hom, fun i => θ.symm (σ i), e₁, e₂, fun s => ?_, fun i Y r z J J' hJ hJ' => ?_⟩
  · have k₁ : ∀ (s' : SecOver G.hom (LB.LinComb L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)))) (c : Fin n → R),
        (∀ j, s'.f j = ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j) ↔
          s' = ∑ i, c i • (show SecOver G.hom _ from σ i) := fun s' c => by
      have : ∀ j, LB.Sec.f (∑ i, c i • (show SecOver G.hom _ from σ i) : SecOver G.hom _) j =
          ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j := fun j =>
        map_sum (chartLin G.hom _ j) _ _
      exact ⟨fun h => SecOver.ext _ _ fun j => (h j).trans (this j).symm, fun h j => h ▸ this j⟩
    have k₂ : ∀ c : Fin n → R, Lin G₀ L₀ k (𝟙 (Over.mk χ)) (fun i => θ.symm (σ i)) (fun i => fnR (c i)) s ↔
        θ s = ∑ i, c i • (show SecOver G.hom _ from σ i) := fun c => by
      have v : ∀ z J, Good L₀ z J → sval (L := L₀) (φ := fun _ : Fin 1 => (snd (Over.mk χ) G₀).left)
          (ε := fun _ => (k : ℤ)) (∑ i, c i • θ.symm (σ i) : SecOver (fst (Over.mk χ) G₀).left _) (𝟙 _) z J =
          ∑ i, gs (fst (Over.mk χ) G₀).left z ⊤ (fnR (c i)) * sval (L := L₀)
            (φ := fun _ : Fin 1 => (snd (Over.mk χ) G₀).left) (ε := fun _ => (k : ℤ)) (θ.symm (σ i))
            ((𝟙 (Over.mk χ)) ▷ G₀).left z J := fun z J hJ => by
        rw [sval_sum' hJ]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sval_smul' hJ, Category.id_comp, id_whiskerRight, Over.id_left]
        rfl
      have u : θ.symm (∑ i, c i • (show SecOver G.hom _ from σ i)) = ∑ i, c i • θ.symm (σ i) :=
        (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => map_smul _ _ _)
      refine Iff.trans ?_ (θ.eq_symm_apply (y := s))
      rw [u]
      exact ⟨fun h => sec_ext' hL₀ fun z J hJ => (h z J hJ).trans (v z J hJ).symm,
        fun h z J hJ => (congrArg (fun q => sval (L := L₀) (φ := fun _ : Fin 1 => (snd (Over.mk χ) G₀).left)
          (ε := fun _ => (k : ℤ)) q (𝟙 _) z J) h).trans (v z J hJ)⟩
    obtain ⟨c, hc, hu⟩ := hσ (θ s)
    refine ⟨fun i => fnR (c i), (k₂ c).2 ((k₁ _ c).1 hc), fun c' hc' => ?_⟩
    obtain ⟨c'', rfl⟩ : ∃ c'' : Fin n → R, c' = fun i => fnR (c'' i) :=
      ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (c' i), funext fun i =>
        (congrArg (fun q => q.hom (c' i)) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id).symm⟩
    rw [hu c'' ((k₁ _ c'').2 ((k₂ c'').1 hc'))]
  · have := hθ (θ.symm (σ i)) Y r z J J' hJ hJ'
    rw [zpow_natCast, Units.val_pow_eq_pow_val] at this
    exact this.trans (congrArg (fun q => _ * sval q r z J') (θ.apply_symm_apply (σ i)))

end Basis

section Expand
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)

theorem exists_expandsG (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k σ f)
    (s : Fam D.toPre F k) (hs : GlobalTheory.ZH.FamOf D.toPre F f s) : ∃ σ' : U.SecGF F k, U.ExpandsG F k σ' s ∧
      ∀ y J, Good U.LG.L y J → sval σ' (𝟙 _) y J = sval σ (UnifPre.gFK (G := G) F) y J := by
  have one : ∀ {Y : Scheme.{0}} (π : Y ⟶ Spec (CommRingCat.of F)) (y : Y), gs (𝟙 Y) y ⊤ (scal π (1 : F)) = 1 :=
    fun π y => by simp only [gs_eq _ y ⊤ trivial, scal, map_one]
  obtain ⟨σ', h⟩ := GlobalTheory.BoxExpansion.exists_secLin U.LG.isLB
    (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (UnifPre.gFK (G := G) F)
    (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (φ := fun _ => 𝟙 G.left) (fun _ => (Category.comp_id _).symm)
    (fun _ : Fin 1 => σ) (fun _ => (1 : F))
  refine ⟨σ', ⟨1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE, h,
    fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩, fun y J hJ => ?_⟩
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm
  · have := (secLin_iff_val U.LG.isLB _ _ _ _).1 h y J hJ
    rwa [Fin.sum_univ_one, one, _root_.one_mul, Category.id_comp] at this

end Expand

theorem exists_bridge : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (χ : Sp R ⟶ Z) (Φ : G.left ⟶ G₀.left) (ω : LB.Iso U.LG.L (L₀.pull Φ)), RigPull G G₀ χ Φ ω U.LG.rig ρ₀ → ∃ (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w₀ : W0 U), RigPull A.A G₀ (jK R ≫ χ) φ w ρ ρ₀ ∧ NormW U w₀ ρ ∧ ∀ (k r : ℕ) (σ : Fin r → H0 U.LG.L k), IsBasisH σ → ∃ b : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk χ)), BasisAlong G₀ L₀ k (𝟙 _) b ∧ ∀ (i : Fin r) (F : Type) [Field F] [Algebra (FractionRing R) F] (f : ∀ α, D.toPre.SecB k α) (s : Fam D.toPre F k) (t : SecA A F k), (∀ e, U.ExpandsAt e k (σ i) f) → GlobalTheory.ZH.FamOf D.toPre F f s → Thru w k (T' := TFK (R := R) F) (T := Over.mk χ) (jFK (R := R) F ≫ jK R) (b i) t → U.ExpandsF F k w₀ t s := by
  intro Z G₀ _ L₀ hL₀ ρ₀ R _ _ I D A G _ _ U χ Φ ω ⟨gp, hω, _, hρ⟩
  obtain ⟨w₀, hw₀⟩ := U.ext
  have := U.gen_hom
  have hg : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have hg' : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left]
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gi : IsGrpPullback A.A ((Over.pullback (jK R)).obj G) (𝟙 _) U.gen.inv.left := isGrpPullback_of_iso U.gen.symm
  have gψ : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    (gi.comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have ei : eSec A.A ≫ U.gen.inv.left = eSec ((Over.pullback (jK R)).obj G) :=
    (GlobalTheory.PolBaseChange.eSec_comm gi).trans (Category.id_comp _)
  have eψ := GlobalTheory.PolBaseChange.eSec_comm gψ
  obtain ⟨w₁, hw₁, Hw₁⟩ := exists_iso_section w₀ hw₀ U.gen.inv.left hg
  obtain ⟨ρ, hρ₁, Hρ⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec A.A) (φ := fun _ => eSec G)
    (ε := fun _ => 1) (h := jK R) ((isGen_iff w₁).2 hw₁) U.LG.isLB A.isLB (fun _ => eψ) U.LG.rig U.LG.rigGen
  obtain ⟨w, T⟩ := exists_comp U.LG.isLB ω w₁ ((isGen_iff ω).1 hω) hw₁ hL₀ A.isLB
  refine ⟨_, w, ρ, w₀, ⟨gψ.comp gp, (isGen_iff w).2 (T.pgen_comp U.LG.isLB ((isGen_iff ω).1 hω) hw₁), hρ₁,
    T.pmaps_comp U.LG.isLB (fun _ => eψ) hρ (pmaps_of_val U.LG.isLB A.isLB (fun _ => eψ) Hρ)⟩,
    ⟨hw₀, hρ₁, fun z JA JG hA hG => ?_⟩, fun k r σ hσ => ?_⟩
  · have a := Hρ _ (𝟙 _) z JG JA hG hA
    rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at a
    have c := Hw₁ _ (eSec A.A) z _ _ (hG (eSec A.A ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) (hA (eSec A.A))
    refine Eq.trans (congrArg (· * _) ?_) a.symm
    refine Eq.trans ?_ c.symm
    rw [eψ, ei]
    rfl
  · obtain ⟨g, b, g₁, g₂, hb, Hb⟩ := exists_basis hL₀ U.LG.isLB gp.1 hω σ hσ
    refine ⟨b, hb, fun i F _ _ f s t hE hs ht => ?_⟩
    obtain ⟨σ', h₁, h₂⟩ := exists_expandsG U F k (σ i) f hE s hs
    have m₁ : (U.genF F).left ≫ (fst (TFK (R := R) F) A.A).left =
        (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
      rw [← Over.comp_left, lift_fst]
    have m₂ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
      rw [← Over.comp_left, lift_snd, Over.comp_left]
    have m₃ : ((snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left) ≫ U.gen.inv.left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by rw [Category.assoc, hg', Category.comp_id]
    have m₄ : ((snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left) ≫ U.gen.inv.left ≫
        pullback.fst G.hom (jK R) = UnifPre.gFK (G := G) F := by rw [← Category.assoc, m₃]
    refine ⟨σ', GlobalTheory.BoxExpansion.isoRel_of_val A.isLB U.LG.isLB m₂ (Category.id_comp _) fun y JA JG hA hG => ?_, h₁⟩
    obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    have a := ht _ (U.genF F).left (UnifPre.gFK (G := G) F ≫ g) (by
      rw [Category.assoc, g₁, ← Category.assoc (U.genF F).left, m₁, Category.assoc, pullback.condition,
        ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ jK R) ((Over.w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G))).trans
        (Over.w (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G))).symm)) (by
      rw [Category.assoc, g₂, ← Category.assoc (U.genF F).left, m₂, ← m₄]
      simp only [Category.assoc]) y J JA hJ hA
    rw [Hb i _ _ y J JG hJ hG, m₂] at a
    generalize hm : (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left = m at a m₃ m₄ ⊢
    have p₁ : (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) (m y) ∈ U.LG.L.U (JG (UnifPre.gFK (G := G) F)) := by
      have := hG (UnifPre.gFK (G := G) F)
      rw [← m₄] at this ⊢
      exact this
    have c := T _ m y _ _ _ (hJ (m ≫ (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ≫ Φ)) p₁ (hA m)
    rw [Hw₁ _ m y _ _ p₁ (hA m), m₃, m₄] at c
    have d : wVal w y J JA m = wVal ω y J JG (UnifPre.gFK (G := G) F) * _ :=
      c.trans (congrArg (· * _) (by rw [wVal, ← Category.assoc m, m₄]))
    rw [d, Units.val_mul, mul_pow, _root_.mul_assoc, ← Units.val_pow_eq_pow_val, Units.mul_right_inj,
      ← Units.val_pow_eq_pow_val] at a
    exact (h₂ y JG hG).trans a

end GlobalTheory.OneBasis.Bridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLogFrame
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch

section Generic
variable {O : Type} [CommRing O] [StarRing O]


omit [StarRing O] in
theorem exists_lift_ct [IsDedekindDomain O] [Module.Finite ℤ O] {V G X : Type} [AddCommGroup V] [Module ℂ V] [CommGroup G]
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module O X] (F : O →+* Module.End ℂ V) (ex : V → G)
    (hadd : ∀ z w, ex (z + w) = ex z * ex w) (hs : Function.Surjective ex) (c : X → G)
    (hc : ∀ x y, c (x + y) = c x * c y) (hl : ∀ (a : O) x z, ex z = c x → ex (F a z) = c (a • x)) :
    ∃ ct : X →+ V, (∀ (a : O) x, ct (a • x) = F a (ct x)) ∧ ∀ x, c x = ex (ct x) := by
  let _ : Module O V := Module.compHom V F
  have e0 : ex 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have c0 : c 0 = 1 := by
    have := hc 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  let P : Submodule O (X × V) :=
    { carrier := {p | ex p.2 = c p.1}
      zero_mem' := e0.trans c0.symm
      add_mem' := fun {p q} hp hq => by
        change ex (p.2 + q.2) = c (p.1 + q.1)
        rw [hadd, hc, (show ex p.2 = _ from hp), (show ex q.2 = _ from hq)]
      smul_mem' := fun a p hp => hl a p.1 p.2 hp }
  obtain ⟨g, hg⟩ := GlobalTheory.Forms.exists_linearMap_lift_of_int (LinearMap.fst O X V ∘ₗ P.subtype)
    (fun x => by
      obtain ⟨z, hz⟩ := hs (c x)
      exact ⟨⟨(x, z), hz⟩, rfl⟩) LinearMap.id
  refine ⟨(LinearMap.snd O X V ∘ₗ P.subtype ∘ₗ g).toAddMonoidHom,
    fun a x => (LinearMap.snd O X V ∘ₗ P.subtype ∘ₗ g).map_smul a x, fun x => ?_⟩
  have h1 : (g x).1.1 = x := hg x
  have h2 : ex (g x).1.2 = c (g x).1.1 := (g x).2
  rw [h1] at h2
  exact h2.symm

theorem exists_log_frame [IsDedekindDomain O] [Module.Finite ℤ O] [Module.Free ℤ O] {N : NumD ℂ} {B : AnArc O}
    {ex : (Fin B.gB → ℂ) → N.A} {fr : (Fin B.gB → ℂ) → ℂˣ} {th : (Fin B.gB → ℂ) → ℂ} (hab : IsAbFrame N.toNumB B ex fr th)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module O X] (e : X ≃+ N.X)
    (ct : X →+ (Fin B.gB → ℂ)) (hc : ∀ x, N.c (e x) = ex (ct x)) {w : O} (hw : w + star w = 1)
    (hbal : ∀ (a : O) y x, (N.τ (e (a • y)) (e x) : ℂ) * fr (ct (a • y) + ct x) * fr (ct y) * fr (ct (star a • x)) =
      N.τ (e y) (e (star a • x)) * fr (ct y + ct (star a • x)) * fr (ct (a • y)) * fr (ct x)) :
    ∃ T : X →+ X →+ ℂ, (∀ x y, T x y = T y x) ∧ (∀ (a : O) y x, T (a • y) x = T y (star a • x)) ∧
      ∀ x y, eTwoPi (T x y) * fr (ct x) * fr (ct y) = N.τ (e x) (e y) * fr (ct x + ct y) := by
  have := GlobalTheory.Forms.projective_of_int O X
  have : Module.Finite O X := Module.Finite.of_restrictScalars_finite ℤ O X
  obtain ⟨T, h1, h2, h3⟩ := GlobalTheory.Forms.exists_log_of_bimul hw
    (fun x y : X => N.τ (e x) (e y) * fr (ct x + ct y) / fr (ct x) / fr (ct y))
    (fun y x x' => by
      have a := congrArg Additive.ofMul (N.τ_add_right (e y) (e x) (e x'))
      have b := congrArg Additive.ofMul (hab.2.2.2.2.2.1 (ct x) (ct x') (ct y))
      apply Additive.ofMul.injective
      simp only [hc, map_add (f := _), add_comm (ct y), ofMul_mul, ofMul_div] at a b ⊢
      linear_combination (norm := abel) a - b)
    (fun y x => by rw [N.τ_symm, add_comm, div_right_comm])
    (fun a y x => by
      have b := hbal a y x
      simp only [← Units.val_mul, Units.val_inj] at b
      replace b := congrArg Additive.ofMul b
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div] at b ⊢
      linear_combination (norm := abel) b)
  refine ⟨AddMonoidHom.mk' (fun x => (T x).toAddMonoidHom) fun x y => by ext; simp, h1, h2, fun x y => ?_⟩
  change Complex.exp (2 * Real.pi * Complex.I * T x y) * _ * _ = _
  rw [← h3]
  simp only [← Units.val_mul, Units.val_inj]
  rw [mul_right_comm, div_mul_cancel, div_mul_cancel]

end Generic

theorem dict_of_val : BrActSt → ValSt → DictSt := by
  intro hBr hVal E _ _ _ H D R _ _ _ A k β hβ
  let _ := H.starRing
  obtain ⟨B, ex, fr, th, hab, hth, hchi, hsig, hF, hros, hprim⟩ := hVal E H D R A
  have := A.closed
  obtain ⟨b1, b2, b3⟩ := hBr R A.D₀ A.even A.bimult ℂ A.N A.ν (𝓞 E) A.oa
  have := A.D₀.freeX
  have := A.D₀.finX
  set e : A.D₀.X ≃+ A.N.X := A.ν.eX.symm with he
  have hee : ∀ x, A.ν.eX (e x) = x := A.ν.eX.apply_symm_apply
  have hw : H.w0 + star H.w0 = 1 := by
    show H.w0 + H.bar H.w0 = 1
    rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]
  obtain ⟨ct, hct, hc⟩ := exists_lift_ct B.F ex hab.1 hab.2.1 (fun x : A.D₀.X => A.N.c (e x))
    (fun x y => by rw [map_add (f := _), A.N.c_add]) (fun a x z hz => A.ν.eA.injective (by
      rw [hF, hz, A.ν.c_eq, A.ν.c_eq, hee, hee, DegPre.cF, DegPre.cF, A.oa.c_lin, Category.assoc]))
  obtain ⟨T, hT1, hT2, hT⟩ := exists_log_frame hab e ct hc hw (fun a y x => by
    obtain ⟨r, hr, h⟩ := b1 a
    have h1 := h (e y) (e x)
    have h2 := hros a (star a) r hr (ct y) (ct x)
    rw [hee, hee, hc, hc] at h1
    rw [← h1, hct, hct]
    linear_combination -(A.N.τ (e (a • y)) (e x) : ℂ) * h2)
  have hact : ∀ (a : 𝓞 E) x, e (a • x) = A.act a (e x) := fun a x => by rw [ArcF.act, hee]
  let B' : An H :=
    { B with
      X := A.D₀.X
      acg := inferInstance
      free := inferInstance
      fin := inferInstance
      mod := inferInstance
      ct := ct
      ct_smul := hct
      T := T
      T_symm := hT1
      T_adj := hT2
      psi := fun x => A.N.ψ (e x) * fr (ct x)
      psi_neg := fun x => by
        rw [map_neg, map_neg, ← hab.2.2.2.2.2.2.1, ← hc, ← _root_.mul_assoc, A.N.even]
      psi_add := fun x y => by
        have h := hT x y
        rw [map_add (f := _), map_add (f := _), A.N.ψ_add]
        push_cast
        linear_combination -(A.N.ψ (e x) : ℂ) * A.N.ψ (e y) * h
      be := β.be.comp e.toIntLinearEquiv.toLinearMap e.toIntLinearEquiv.toLinearMap
      be_symm := fun x y => β.symm _ _
      be_pos := fun x hx => β.pos _ fun h => hx (e.map_eq_zero_iff.1 h)
      be_adj := fun a y x => by
        change β.be (e (a • y)) (e x) = β.be (e y) (e (star a • x))
        rw [hact, hact]
        exact hβ a _ _
      be_even := fun x => (dvd_mul_right 2 (k : ℤ)).trans (β.dvd _ _) }
  have hab' : IsAbFrame A.N.toNumB B' ex fr th := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hab
    refine ⟨a1, a2, a3, a4, a5, a6, a7, ⟨a8.1, fun l z => ?_⟩, a9⟩
    have := a8.2 l z
    rw [map_zero] at this ⊢
    exact this
  refine ⟨B', ⟨e, ex, fr, th, hab', hc, fun _ => rfl⟩, ⟨hact, ?_⟩, fun _ _ => rfl, ⟨hw, hchi, fun y => ?_⟩, hth, hsig⟩
  · rintro a g g' c c' v hg hg' hgg ⟨hv1, hv2⟩
    obtain ⟨r, hr, h⟩ := b2 a
    obtain ⟨h1, h2⟩ := h g g' c c' hg hg' hgg
    change c.b = ex v.2 at hv1
    refine ⟨A.ν.eA.injective (by rw [h1, hv1]; exact (hF a v.2).symm), fun x : A.D₀.X => ?_⟩
    have h3 := h2 (e x)
    have h4 : (c.s (e (star a • x)) : ℂ) * fr (ct (star a • x) + v.2) =
      eTwoPi (v.1 (star a • x)) * fr (ct (star a • x)) * fr v.2 := hv2 (star a • x)
    have h5 := hros (star a) a r hr (ct x) v.2
    rw [hee, hc, hv1] at h3
    rw [hct] at h4
    change (c'.s (e x) : ℂ) * fr (ct x + B.F a v.2) = eTwoPi (v.1 (star a • x)) * fr (ct x) * fr (B.F a v.2)
    refine mul_right_cancel₀ (mul_ne_zero (fr (B.F (star a) (ct x))).ne_zero (fr v.2).ne_zero) ?_
    rw [h3]
    linear_combination (c.s (e (star a • x)) : ℂ) * h5 + (fr (ct x) : ℂ) * fr (B.F a v.2) * h4
  · obtain ⟨t, ht, h⟩ := b3 H.w0 A.w0
    have h1 := h (e y)
    have h2 := hprim t ht (ct y)
    have h3 := hT y (H.w0 • y)
    rw [hee, hc] at h1
    rw [hct] at h3
    change ((A.N.ψ (e y) * fr (ct y) : ℂˣ) : ℂ) = eTwoPi (T y (H.w0 • y))
    refine mul_right_cancel₀ (mul_ne_zero (fr (ct y)).ne_zero (fr (B.F H.w0 (ct y))).ne_zero) ?_
    rw [Units.val_mul, ← h1]
    linear_combination (A.N.τ (e y) (e (H.w0 • y)) : ℂ) * h2 - h3

end GlobalTheory.Ex.Arch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniversalSectionBasisPolarisedFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.Ex.OneGen

theorem existsUnique_smul_of_basis {R M κ : Type} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton κ]
    (c : Module.Basis κ R M) (k : κ) (s : M) : ∃! r : R, s = r • c k := by
  have := uniqueOfSubsingleton k
  obtain rfl : k = default := Subsingleton.elim _ _
  refine ⟨c.repr s default, ?_, fun r hr => ?_⟩
  · have e := c.sum_repr s
    rw [Fintype.sum_unique] at e
    exact e.symm
  · rw [hr]; simp

theorem exists_univBasis_field (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K]
    (y : Sp K ⟶ S) : ∃ b : SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk y), ∀ (T : Over S) [IsAffine T.left] (h : T ⟶ Over.mk y)
      (s : SecM P.A P.L ((1 : ℕ) : ℤ) T), ∃! c : Γ(T.left, ⊤), s = c • VVRank.pullM P.A P.L _ h b := by
  obtain ⟨V, hV, b, hb⟩ := ThetaReal.exists_univBasis hS P 1 le_rfl (y (closedPoint K))
  have hr : Set.range y ⊆ Set.range V.ι := by
    rintro _ ⟨q, rfl⟩
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rw [Subsingleton.elim q (closedPoint K)]
    exact ⟨⟨_, hV⟩, rfl⟩
  let u : Over.mk y ⟶ overRes (T := baseOver S) V := Over.homMk (IsOpenImmersion.lift V.ι y hr)
    ((congrArg (_ ≫ ·) (Category.comp_id V.ι)).trans (IsOpenImmersion.lift_fac V.ι y hr))
  have h1 : 1 ^ P.g = 1 := one_pow _
  let k₀ : Fin (1 ^ P.g) := Fin.cast h1.symm 0
  have : Subsingleton (Fin (1 ^ P.g)) := ⟨fun a a' => Fin.ext (by have := a.2; have := a'.2; omega)⟩
  refine ⟨VVRank.pullM P.A P.L _ u (b k₀), fun T _ h s => ?_⟩
  obtain ⟨c, hc⟩ := hb T (h ≫ u)
  rw [VVRank.pullM_comp _ P.isLB, ← hc]
  exact existsUnique_smul_of_basis c k₀ s

theorem exists_univBasis_of_fibre : Laws2 → ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB →
    ∀ (P : PolAV S') (f : S' ⟶ S) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G f φ → LBIso P.L (L.pull φ) →
    ∀ (K : Type) [Field K] (y : Sp K ⟶ S') (x : Sp K ⟶ S), y ≫ f = x → ∃ e, UnivBasis G L x e := by
  intro hL S S' G _ L hL₀ P f φ hp hw K _ y x hx
  obtain ⟨w, hw⟩ := hw
  obtain ⟨b, hb⟩ := exists_univBasis_field hL.secBaseChangeAny P y
  have hτ : (𝟙 (Sp K) : (Over.mk y).left ⟶ (Over.mk x).left) ≫ (Over.mk x).hom = (Over.mk y).hom ≫ f :=
    (Category.id_comp _).trans hx.symm
  have : IsIso (C := Scheme.{0}) (X := (Over.mk y).left) (Y := (Over.mk x).left) (𝟙 (Sp K)) := IsIso.id _
  obtain ⟨e, he⟩ := UnivBasisMove.exists_rel_up hp (T := Over.mk y) (T₀ := Over.mk x) (𝟙 (Sp K)) hτ hw hL₀ P.isLB b
  refine ⟨SecM.toSec G e, fun K' _ i x' h s => ?_⟩
  obtain rfl : (spMap i ≫ y) ≫ f = x' := by rw [Category.assoc, hx, h]
  let T : Over S' := Over.mk (spMap i ≫ y)
  have : IsAffine T.left := inferInstanceAs (IsAffine (Spec _))
  obtain ⟨E, hE⟩ := UnivBasisMove.exists_linearEquiv hp hw hL₀ P.isLB ((1 : ℕ) : ℤ) T
  let u : T ⟶ Over.mk y := Over.homMk (spMap i) rfl
  let u₀ : Over.mk (T.hom ≫ f) ⟶ Over.mk x := Over.homMk (spMap i) h
  have key : E (VVRank.pullM G L _ u₀ e) = VVRank.pullM P.A P.L _ u b :=
    (hE _).unique_down hL₀ P.isLB (he.pull _ _ u u₀ ((Category.id_comp _).trans (Category.comp_id _).symm))
  obtain ⟨c, hc, hu⟩ := hb T u (E s)
  refine ⟨c, E.injective (hc.trans ?_), fun r hr => hu r ?_⟩
  · rw [← key]
    exact (E.map_smul c _).symm
  · rw [← key]
    exact (congrArg E hr).trans (E.map_smul r _)

end GlobalTheory.Ex.OneGen
end
end

