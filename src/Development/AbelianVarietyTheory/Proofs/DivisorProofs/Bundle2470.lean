module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUniv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullDegTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem psi_val_on {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') {W : (Sp R).Opens}
    (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ) (x : D'.X) (z : (TK R').left)
    {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val (ψW.psi (h.xe x)) g z J = (om h.w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J' := by
  have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
  have ag : val (ψW.psi (h.xe x)) g z J = val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J :=
    ArcSpecialise.psiOn_agree ψW h.psiW _ _ _ (by rw [hg, Category.id_comp, h.g_comm]) hJ
  change _ = (om h.w z J J' (𝟙 _ ≫ D'.xK x))⁻¹ * _ at v
  rw [ag, v, Category.id_comp]

def reopen {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') {W : (Sp R).Opens}
    (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ) : IsPullDeg φ D D' :=
  { h with
    W := W
    psiW := ψW
    g := g
    g_comm := hg
    psi_pr := fun x => by
      obtain ⟨b, hb, hc⟩ := h.psi_pr x
      refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (val_corr hJ hc (𝟙 _)).trans ?_⟩
      rw [val_pull hJ, val_pull hJ]
      exact ArcSpecialise.psiOn_agree h.psiW ψW _ _ _ (by
        rw [Category.id_comp, Category.id_comp, hg, h.g_comm]) hJ }

theorem exists_top {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D')
    (hU : ∀ y, PsiUnitOn D y Set.univ) : ∃ h' : IsPullDeg φ D D', h'.W = ⊤ ∧ proj h' = proj h ∧ h'.xe = h.xe := by
  obtain ⟨ψ⟩ := nonempty_psiOn_top D hU
  exact ⟨reopen h ψ ((jK R' ≫ specOf φ) ≫ (Sp R).topIso.inv) (by
    rw [Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id]), rfl, rfl, rfl⟩

theorem psiUnitOn_univ {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D')
    (hU : ∀ y, PsiUnitOn D y Set.univ) (x : D'.X) : PsiUnitOn D' x Set.univ := by
  obtain ⟨h', hW, -, -⟩ := exists_top h hU
  obtain ⟨ψ, -⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull h'
  have := GlobalTheory.PsiUnitOfPsiOn.psiUnitOn_of_psiOn _ _ _ ψ x
  rw [hW] at this
  exact this

theorem act_iff {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') (f : D.P.A ⟶ D.P.A)
    (f' : D'.P.A ⟶ D'.P.A) :
    f' ≫ h.e.hom = h.e.hom ≫ (Over.pullback (specOf φ)).map f ↔ f'.left ≫ proj h = proj h ≫ f.left := by
  have a : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst D.P.A.hom (specOf φ) =
      pullback.fst D.P.A.hom (specOf φ) ≫ f.left := by
    simp [Over.pullback_map_left, pullback.lift_fst]
  constructor
  · intro H
    have := congrArg (fun q => q.left ≫ pullback.fst D.P.A.hom (specOf φ)) H
    simp only [Over.comp_left, Category.assoc] at this
    rw [a] at this
    exact this.trans (Category.assoc _ _ _).symm
  · intro H
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      rw [a]
      exact H.trans (Category.assoc _ _ _)
    · exact (Over.w (f' ≫ h.e.hom)).trans (Over.w (h.e.hom ≫ (Over.pullback (specOf φ)).map f)).symm

theorem exists_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p₀ : IsPullDeg i D D') (q : IsPullDeg j D' D'')
    (hU : ∀ y, PsiUnitOn D y Set.univ) :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p₀ ∧ ∀ x, r.xe x = p₀.xe (q.xe x) := by
  obtain ⟨p, hW, e₁, e₂⟩ := exists_top p₀ hU
  rw [← e₁, ← e₂]
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨ψ, hv⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull p
  obtain ⟨g, hg⟩ : ∃ g : (TK R'').left ⟶ (specOf i ⁻¹ᵁ p.W).toScheme,
      g ≫ (specOf i ⁻¹ᵁ p.W).ι = jK R'' ≫ specOf j :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hg' : (g ≫ (specOf i ∣_ p.W)) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, hr₁, hr₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW D D'' p.psiW (g ≫ (specOf i ∣_ p.W)) hg' gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := hv (q.xe x) _ g z J J' hJ hJ'
      have v₂ := psi_val_on q ψ g hg x z hJ' hJ''
      have hx : D''.xK x ≫ proj q = g ≫ (specOf i ⁻¹ᵁ p.W).ι ≫ (D'.c (q.xe x)).left := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = _
        rw [Category.assoc, q.c_pr, ← Category.assoc g, hg, Category.assoc]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      rw [v₂, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, hr₁, hr₂⟩

theorem exists_cancel {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁]
    [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} {θ : R₀ →+* R₂} (hθ : β.comp α = θ)
    {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂}
    (h₀ : IsPullDeg α D₀ D₁) (h : IsPullDeg θ D₀ D) (hU : ∀ y, PsiUnitOn D₀ y Set.univ) :
    ∃ h' : IsPullDeg β D₁ D, proj h' ≫ proj h₀ = proj h ∧ ∀ x, h₀.xe (h'.xe x) = h.xe x := by
  subst hθ
  obtain ⟨h₁, hW₁, e₁', e₂'⟩ := exists_top h₀ hU
  rw [← e₁', ← e₂']
  have hW : specOf α ⁻¹ᵁ h₁.W = ⊤ := by rw [hW₁]; rfl
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW, hv⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull h₁
  obtain ⟨g, hg⟩ : ∃ g : (TK R₂).left ⟶ (specOf α ⁻¹ᵁ h₁.W).toScheme,
      g ≫ (specOf α ⁻¹ᵁ h₁.W).ι = jK R₂ ≫ specOf β :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨hD, k₁, k₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW D₁ D ψW g hg gp w hw hr xe hc
    (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ₀ hJ
    have v₁ := hv (xe x) _ g z J₀ J₁ hJ₀ hJ₁
    have ag : val (h₁.psiW.psi (h.xe x)) (g ≫ (specOf α ∣_ h₁.W)) z J₀ =
        val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J₀ :=
      ArcSpecialise.psiOn_agree h₁.psiW h.psiW _ _ _ (by
        rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg, Category.id_comp, h.g_comm, Category.assoc]
        exact congrArg (jK R₂ ≫ ·) sc) hJ₀
    have hx : D.xK x ≫ Φ = g ≫ (specOf α ⁻¹ᵁ h₁.W).ι ≫ (D₁.c (xe x)).left := by
      show (jK R₂ ≫ (D.c x).left) ≫ Φ = _
      rw [Category.assoc, hc, ← Category.assoc g, hg, Category.assoc]
    change _ = (om h.w z J₀ J (𝟙 _ ≫ D.xK x))⁻¹ * _ at v
    rw [hxe, ag, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD, by rw [k₁, e₁], fun x => by rw [k₂, hxe]⟩

theorem main : (∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (_ : IsPullDeg φ D D'), (∀ y, PsiUnitOn D y Set.univ) → ∀ x, PsiUnitOn D' x Set.univ) ∧ (∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') (f : D.P.A ⟶ D.P.A) (f' : D'.P.A ⟶ D'.P.A), f' ≫ h.e.hom = h.e.hom ≫ (Over.pullback (specOf φ)).map f ↔ f'.left ≫ h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = (h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ f.left) ∧ (∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), (∀ y, PsiUnitOn D y Set.univ) → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x)) ∧ (∀ {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁] [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} {θ : R₀ →+* R₂}, β.comp α = θ → ∀ {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂} (h₀ : IsPullDeg α D₀ D₁) (h : IsPullDeg θ D₀ D), (∀ y, PsiUnitOn D₀ y Set.univ) → ∃ h' : IsPullDeg β D₁ D, (h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf β)) ≫ h₀.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf α) = h.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ) ∧ ∀ x, h₀.xe (h'.xe x) = h.xe x) :=
  ⟨fun h hU x => psiUnitOn_univ h hU x, fun h f f' => act_iff h f f', fun p q hU => exists_comp p q hU,
    fun e _ _ _ h₀ h hU => exists_cancel e h₀ h hU⟩

end GlobalTheory.PullDegTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationsSameGenericFibreAgreeAtPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Points
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Special

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

section Model

variable {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
  [Algebra Ω Ω'] {M : RatModel o Ω} {M' : RatModel o' Ω'} {f : M'.Z ⟶ M.Z}

theorem valF_app_of (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {U : M.Z.Opens}
    (hU : (U : Set M.Z).Nonempty) (a : Γ(M.Z, U)) :
    valF M'.pt (f ⁻¹ᵁ U) (f.app U a) = algebraMap Ω Ω' (valF M.pt U a) := by
  refine (valR_comp M'.pt f U a).symm.trans ?_
  rw [hf]
  exact valR_spMap_comp _ M.pt U (M.top_le_preimage_pt hU) a

theorem map_mem_O_of (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {z : M'.Z} {x : Ω}
    (hx : x ∈ M.O (f z)) : algebraMap Ω Ω' x ∈ M'.O z := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  exact ⟨f ⁻¹ᵁ U, f.app U a, hz, valF_app_of hf ⟨_, hz⟩ a⟩

theorem val_comp_of (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {K : Type} [Field K] (y : Sp K ⟶ M'.Z)
    (w : Sp K) {x : Ω} (hx : x ∈ M.O (f (y w))) : M.val (y ≫ f) x = M'.val y (algebraMap Ω Ω' x) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ (f ⁻¹ᵁ U : M'.Z.Opens) := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [RatModel.val_eq h1 (valF_app_of hf ⟨_, hz⟩ a), RatModel.val_valF (U := U) (by rintro _ ⟨w', rfl⟩; exact h1 ⟨w', rfl⟩)]
  exact valR_comp y f U a

end Model

section Pts

variable {K C : Type} [CommRing K] [CommRing C] {A : Over (Sp K)}

theorem pt_iff_eq {R : Type} [CommRing R] {G : Over (Sp R)} {h : R →+* K} {a : A.left ⟶ G.left}
    (c : IsPullback a A.hom G.hom (spMap h)) (j : K →+* C) {s : Sp R ⟶ G.left} {w : Sp K ⟶ A.left}
    (hw : w ≫ A.hom = 𝟙 _) (hs : w ≫ a = spMap h ≫ s) (x : Sp C ⟶ A.left) (hx : x ≫ A.hom = spMap j) :
    x ≫ a = spMap (j.comp h) ≫ s ↔ x = spMap j ≫ w := by
  rw [spMap_comp', Category.assoc, ← hs]
  constructor
  · intro e
    exact c.hom_ext (by rw [e, Category.assoc]) (by rw [hx, Category.assoc, hw, Category.comp_id])
  · intro e
    rw [e, Category.assoc]

theorem end_iff_eq {S : Scheme.{0}} {G : Over S} {f : Sp K ⟶ S} {a : A.left ⟶ G.left}
    (c : IsPullback a A.hom G.hom f) {ε : G.left ⟶ G.left} {e : A.left ⟶ A.left} (he : e ≫ A.hom = A.hom)
    (he' : e ≫ a = a ≫ ε) {T : Scheme.{0}} (x x' : T ⟶ A.left) (hx : x' ≫ A.hom = x ≫ A.hom) :
    x' ≫ a = x ≫ a ≫ ε ↔ x' = x ≫ e := by
  rw [← he', ← Category.assoc]
  constructor
  · intro k
    exact c.hom_ext k (by rw [Category.assoc, he, hx])
  · intro k
    rw [k]

end Pts

end GlobalTheory.Poinc.Special

theorem GlobalTheory.Poinc.Special.specialise_sameAt : ∀ (R₁ R₂ B K M Γ : Type) [CommRing R₁] [CommRing R₂] [CommRing B] [CommRing K] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂)) (f₁ : R₁ →+* B) (f₂ : R₂ →+* B) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A)) (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)), SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ → (∀ τ : B →+* B, τ.comp f₂ = f₂ → τ = RingHom.id B) → ∀ (v : B →+* K) (A₁ : PolAV (Sp K)) (a₁ : A₁.A.left ⟶ P₁.A.left), IsGrpPullback A₁.A P₁.A (spMap (v.comp f₁)) a₁ → LBIso A₁.L (P₁.L.pull a₁) → ∃ φ₂ : A₁.A.left ⟶ P₂.A.left, IsGrpPullback A₁.A P₂.A (spMap (v.comp f₂)) φ₂ ∧ LBIso A₁.L (P₂.L.pull φ₂) ∧ (∀ E, ∃ e : A₁.A.left ⟶ A₁.A.left, e ≫ A₁.A.hom = A₁.A.hom ∧ e ≫ a₁ = a₁ ≫ (e₁ E).left ∧ e ≫ φ₂ = φ₂ ≫ (e₂ E).left) ∧ ∀ x, ∃ w : Sp K ⟶ A₁.A.left, w ≫ A₁.A.hom = 𝟙 _ ∧ w ≫ a₁ = spMap (v.comp f₁) ≫ (t₁ x).left ∧ w ≫ φ₂ = spMap (v.comp f₂) ≫ (t₂ x).left := by
  intro R₁ R₂ B K M Γ _ _ _ _ P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ hS hrig v A₁ a₁ ha₁ hL₁
  obtain ⟨P, b₁, b₂, hb₁, hb₂, hLb₁, hLb₂, hε, ht⟩ := hS
  have hv₁ : spMap (v.comp f₁) = spMap v ≫ spMap f₁ := GlobalTheory.Poinc.Special.spMap_comp' f₁ v
  have hv₂ : spMap (v.comp f₂) = spMap v ≫ spMap f₂ := GlobalTheory.Poinc.Special.spMap_comp' f₂ v
  have sq : a₁ ≫ P₁.A.hom = (A₁.A.hom ≫ spMap v) ≫ spMap f₁ := by
    rw [ha₁.1.w, hv₁, Category.assoc]
  let b : A₁.A.left ⟶ P.A.left := hb₁.1.lift a₁ (A₁.A.hom ≫ spMap v) sq
  have hb_a : b ≫ b₁ = a₁ := hb₁.1.lift_fst _ _ _
  have hb_s : b ≫ P.A.hom = A₁.A.hom ≫ spMap v := hb₁.1.lift_snd _ _ _
  have hbP : IsGrpPullback A₁.A P.A (spMap v) b :=
    IsGrpPullback.cancel hb₁ (ha₁.congr hv₁ hb_a.symm) hb_s
  refine ⟨b ≫ b₂, (hbP.comp hb₂).congr hv₂.symm rfl, ?_, fun E => ?_, fun x => ?_⟩
  · have i1 : LBIso (P.L.pull b) (P₁.L.pull a₁) := GlobalTheory.PolDeg.lbIso_pull_comp hLb₁ b hb_a.symm
    have i2 : LBIso (P.L.pull b) (P₂.L.pull (b ≫ b₂)) := GlobalTheory.PolDeg.lbIso_pull_comp hLb₂ b rfl
    exact (hL₁.trans A₁.isLB (pull_isLB P₁.isLB _) (pull_isLB P.isLB _) i1.symm).trans A₁.isLB
      (pull_isLB P.isLB _) (pull_isLB P₂.isLB _) i2
  · obtain ⟨eP, heP₁, heP₂⟩ := hε E
    have sqe : (a₁ ≫ (e₁ E).left) ≫ P₁.A.hom = A₁.A.hom ≫ spMap (v.comp f₁) := by
      rw [Category.assoc, Over.w (e₁ E), ha₁.1.w]
    let e : A₁.A.left ⟶ A₁.A.left := ha₁.1.lift (a₁ ≫ (e₁ E).left) A₁.A.hom sqe
    have he₁ : e ≫ a₁ = a₁ ≫ (e₁ E).left := ha₁.1.lift_fst _ _ _
    have he : e ≫ A₁.A.hom = A₁.A.hom := ha₁.1.lift_snd _ _ _
    have heb : e ≫ b = b ≫ eP.left := hb₁.1.hom_ext
      (by rw [Category.assoc, hb_a, he₁, Category.assoc, heP₁, ← Category.assoc, hb_a])
      (by rw [Category.assoc, hb_s, ← Category.assoc, he, Category.assoc, Over.w eP, hb_s])
    exact ⟨e, he, he₁, by rw [← Category.assoc, heb, Category.assoc, heP₂, Category.assoc]⟩
  · obtain ⟨w, hw₁, hw₂⟩ := ht x
    have hσ : spMap ((Spec.preimage (w ≫ P.A.hom)).hom) = w ≫ P.A.hom := by
      rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    have hσ₂ : (w ≫ P.A.hom) ≫ spMap f₂ = spMap f₂ := by
      rw [Category.assoc, ← hb₂.1.w, ← Category.assoc, hw₂, Category.assoc, Over.w (t₂ x)]
      exact Category.comp_id _
    have hτ : (Spec.preimage (w ≫ P.A.hom)).hom.comp f₂ = f₂ := by
      have h1 : spMap ((Spec.preimage (w ≫ P.A.hom)).hom.comp f₂) = spMap f₂ := by
        rw [GlobalTheory.Poinc.Special.spMap_comp', hσ, hσ₂]
      exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h1)
    have hwP : w ≫ P.A.hom = 𝟙 _ := by
      rw [← hσ, hrig _ hτ]
      exact Spec.map_id _
    have sqt : (spMap (v.comp f₁) ≫ (t₁ x).left) ≫ P₁.A.hom = 𝟙 _ ≫ spMap (v.comp f₁) := by
      rw [Category.assoc, Over.w (t₁ x), Category.id_comp]
      exact Category.comp_id _
    let w' : Sp K ⟶ A₁.A.left := ha₁.1.lift (spMap (v.comp f₁) ≫ (t₁ x).left) (𝟙 _) sqt
    have hw'₁ : w' ≫ a₁ = spMap (v.comp f₁) ≫ (t₁ x).left := ha₁.1.lift_fst _ _ _
    have hw' : w' ≫ A₁.A.hom = 𝟙 _ := ha₁.1.lift_snd _ _ _
    have hw'b : w' ≫ b = spMap v ≫ w := hb₁.1.hom_ext
      (by rw [Category.assoc, hb_a, hw'₁, hv₁, Category.assoc, Category.assoc, hw₁])
      (by rw [Category.assoc, hb_s, ← Category.assoc, hw', Category.id_comp, Category.assoc, hwP,
        Category.comp_id])
    exact ⟨w', hw', hw'₁, by rw [← Category.assoc, hw'b, Category.assoc, hw₂, hv₂, Category.assoc]⟩


open GlobalTheory.Poinc.Special in
theorem GlobalTheory.Poinc.special_transport : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) →
  ∀ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)), Same ρ' ε' ρ₂ ε₂ (fun a => D.lab a) (algebraMap X₁.Ω₁ D.X.Ω₁) → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) →
  ∀ (K : Type) [Field K] (j : K →+* PadicAlgCl p) (f' : R' →+* K), j.comp f' = y₀ → (∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))), D.X.M.val (gPt p ≫ y) a ∈ j.range) →
  ∀ (A₁ : PolAV (Sp K)) (a₁ : A₁.A.left ⟶ ρ'.P.A.left), IsGrpPullback A₁.A ρ'.P.A (spMap f') a₁ → LBIso A₁.L (ρ'.P.L.pull a₁) →
  ∃ (f₂ : R₂ →+* K) (φ₂ : A₁.A.left ⟶ ρ₂.P.A.left), j.comp f₂ = y₂ ∧ IsGrpPullback A₁.A ρ₂.P.A (spMap f₂) φ₂ ∧ LBIso A₁.L (ρ₂.P.L.pull φ₂) ∧
    (∀ (x : Sp (PadicAlgCl p) ⟶ A₁.A.left) (a : X₁.S.Gam), x ≫ A₁.A.hom = spMap j → (x ≫ φ₂ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ x ≫ a₁ = spMap y₀ ≫ (ρ'.pt a).left)) ∧
    (∀ (x x' : Sp (PadicAlgCl p) ⟶ A₁.A.left) (E : Matrix (Fin 8) (Fin 8) ℤ), x ≫ A₁.A.hom = spMap j → x' ≫ A₁.A.hom = spMap j → (x' ≫ φ₂ = x ≫ φ₂ ≫ (ε₂ E).left ↔ x' ≫ a₁ = x ≫ a₁ ≫ (ε' E).left)) := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D p _ z₁ c y h c₀ hc R' fg frac hth hev ρ' ε' hR' y₀ hy₀ c₂ hc₂ R₂ fg₂ frac₂
    hth₂ hev₂ ρ₂ ε₂ hsame hR₂ y₂ hy₂ K _ j f' hf' hval A₁ a₁ ha₁ hL₁

  set x₂ := (gPt p ≫ y) (closedPoint (PadicAlgCl p)) with hx₂
  have hx₁ : (gPt p ≫ c.y) (closedPoint (PadicAlgCl p)) = D.q x₂ := by
    rw [← h, ← Category.assoc]; rfl
  haveI : IsDedekindDomain D.X.o₁ := ArithBase.ded (Ω := D.X.Ω₁)
  haveI : IsNoetherianRing (D.X.M.O x₂) := D.X.M.isNoetherianRing_O x₂
  haveI : IsIntegrallyClosed (D.X.M.O x₂) := haveI := D.X.normal; RatModel.isIntegrallyClosed_O (GlobalTheory.IsNormalScheme.pred _) x₂
  have hmem : ∀ a : R', algebraMap X₁.Ω₁ D.X.Ω₁ a ∈ D.X.M.O x₂ := fun a =>
    map_mem_O_of D.gen (hx₁ ▸ hR' a.2)
  let g₁ : R' →+* D.X.M.O x₂ := ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom).codRestrict _ hmem
  let g₂ : R₂ →+* D.X.M.O x₂ := (Subalgebra.inclusion hR₂).toRingHom
  have e₁ : (algebraMap (D.X.M.O x₂) D.X.Ω₁).comp g₁ = (algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom :=
    RingHom.ext fun _ => rfl
  have e₂ : (algebraMap (D.X.M.O x₂) D.X.Ω₁).comp g₂ = R₂.val.toRingHom := RingHom.ext fun _ => rfl

  have hS₀ : SameAt ρ'.P ρ₂.P ((algebraMap (D.X.M.O x₂) D.X.Ω₁).comp g₁) ((algebraMap (D.X.M.O x₂) D.X.Ω₁).comp g₂)
      ε' ε₂ ρ'.pt (fun a => ρ₂.pt (D.lab a)) := by
    rw [e₁, e₂]
    obtain ⟨P₀, a, a', ε₀, h1, h2, h3, h4, h5, h6⟩ := hsame
    exact ⟨P₀, a, a', h1, h2, h3, h4, fun E => ⟨ε₀ E, (h5 E).1, (h5 E).2⟩, h6⟩
  have hSO := GlobalTheory.Poinc.sameAt_of_generic _ _ _ _ _ _ ρ'.P ρ₂.P g₁ g₂ ε' ε₂ _ _ hS₀

  let vO : D.X.M.O x₂ →+* PadicAlgCl p :=
    D.X.M.valHom (gPt p ≫ y) x₂ (RatModel.range_eq_singleton _ _)
  have hvr : ∀ a, vO a ∈ j.range := fun a => hval a a.2
  let jE : K ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict ⟨fun a b hab => j.injective
    (congrArg Subtype.val hab), j.rangeRestrict_surjective⟩
  let v : D.X.M.O x₂ →+* K := jE.symm.toRingHom.comp (vO.codRestrict j.range hvr)
  have hjv : ∀ a, j (v a) = vO a := fun a => congrArg Subtype.val (jE.apply_symm_apply (vO.codRestrict j.range hvr a))
  have hf₂ : j.comp (v.comp g₂) = y₂ := RingHom.ext fun a => (hjv _).trans (hy₂ a).symm
  have hf'v : f' = v.comp g₁ := RingHom.ext fun a => j.injective <| by
    rw [← RingHom.comp_apply j f', hf', hy₀ a, RingHom.comp_apply, hjv]
    show X₁.M.val (gPt p ≫ c.y) a = D.X.M.val (gPt p ≫ y) (algebraMap X₁.Ω₁ D.X.Ω₁ a)
    rw [← h, ← Category.assoc]
    have hm : (a : X₁.Ω₁) ∈ X₁.M.O (D.q ((gPt p ≫ y) (closedPoint (PadicAlgCl p)))) := hx₁ ▸ hR' a.2
    exact val_comp_of D.gen (gPt p ≫ y) (closedPoint (PadicAlgCl p)) hm
  subst hf'v
  have hrig : ∀ τ : D.X.M.O x₂ →+* D.X.M.O x₂, τ.comp g₂ = g₂ → τ = RingHom.id _ := by
    intro τ hτ
    refine RingHom.ext fun x => ?_
    show τ x = x
    obtain ⟨a, ha, b, hb, hab⟩ := frac₂ x
    have hτa : ∀ r : R₂, τ (g₂ r) = g₂ r := fun r => RingHom.congr_fun hτ r
    by_cases hb0 : b = 0
    · have hx0 : x = 0 := Subtype.ext (by rw [hab, hb0, div_zero]; rfl)
      rw [hx0, map_zero]
    · have key : g₂ ⟨b, hb⟩ * x = g₂ ⟨a, ha⟩ := Subtype.ext (by
        show b * (x : D.X.Ω₁) = a
        rw [hab, mul_div_cancel₀ _ hb0])
      have h0 : g₂ ⟨b, hb⟩ ≠ 0 := fun h0 => hb0 (congrArg Subtype.val h0)
      have key' := congrArg τ key
      rw [map_mul, hτa, hτa, ← key] at key'
      exact mul_left_cancel₀ h0 key'
  obtain ⟨φ₂, hφ₂, hL₂, hε, ht⟩ := (GlobalTheory.Poinc.Special.specialise_sameAt) _ _ _ _ _ _ ρ'.P ρ₂.P g₁ g₂ ε' ε₂ _ _ hSO hrig v A₁ a₁ ha₁ hL₁
  refine ⟨v.comp g₂, φ₂, hf₂, hφ₂, hL₂, fun x a hx => ?_, fun x x' E hx hx' => ?_⟩
  · obtain ⟨w, hw, hw₁, hw₂⟩ := ht a
    rw [← hf₂, ← hf', pt_iff_eq hφ₂.1 j hw hw₂ x hx, pt_iff_eq ha₁.1 j hw hw₁ x hx]
  · obtain ⟨e, he, he₁, he₂⟩ := hε E
    rw [end_iff_eq hφ₂.1 he he₂ x x' (hx'.trans hx.symm), end_iff_eq ha₁.1 he he₁ x x' (hx'.trans hx.symm)]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RechartingsThetaSetupSameGeometricFibreAtTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.Spread.noeth (o Ω : Type) [CommRing o] [IsNoetherianRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (z : M.Z) : IsNoetherianRing (M.O z) := by
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  exact isNoetherianRing_of_ringEquiv _ (M.stalkEquiv z)

theorem GlobalTheory.Poinc.Spread.endo_id {R O : Type} [CommRing R] [CommRing O] [IsDomain O] (f : R →+* O)
    (hf : ∀ o : O, ∃ a b : R, f b ≠ 0 ∧ f b * o = f a) (σ : Sp O ⟶ Sp O) (h : σ ≫ spMap f = spMap f) : σ = 𝟙 _ := by
  obtain ⟨s, rfl⟩ := Spec.map_surjective σ
  rw [← Spec.map_comp] at h
  have h' := Spec.map_injective h
  have hs : ∀ r, s.hom (f r) = f r := fun r => congrArg (fun g => g.hom r) h'
  have : s = 𝟙 _ := by
    ext o
    obtain ⟨a, b, hb, e⟩ := hf o
    have e2 := congrArg s.hom e
    rw [map_mul, hs, hs, ← e] at e2
    exact mul_left_cancel₀ hb e2
  rw [this, Spec.map_id]

theorem GlobalTheory.Poinc.Spread.sec {R₁ R₂ O M Γ : Type} [CommRing R₁] [CommRing R₂] [CommRing O] [IsDomain O] {P₁ : PolAV (Sp R₁)} {P₂ : PolAV (Sp R₂)} {f₁ : R₁ →+* O} {f₂ : R₂ →+* O} {e₁ : M → (P₁.A ⟶ P₁.A)} {e₂ : M → (P₂.A ⟶ P₂.A)} {t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)} {t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)}
    (hf : ∀ o : O, ∃ a b : R₁, f₁ b ≠ 0 ∧ f₁ b * o = f₁ a) (h : SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂) :
    ∃ (P : PolAV (Sp O)) (b₁ : P.A.left ⟶ P₁.A.left) (b₂ : P.A.left ⟶ P₂.A.left), IsGrpPullback P.A P₁.A (spMap f₁) b₁ ∧ IsGrpPullback P.A P₂.A (spMap f₂) b₂ ∧ LBIso P.L (P₁.L.pull b₁) ∧ LBIso P.L (P₂.L.pull b₂) ∧ (∀ E, ∃ e : P.A ⟶ P.A, e.left ≫ b₁ = b₁ ≫ (e₁ E).left ∧ e.left ≫ b₂ = b₂ ≫ (e₂ E).left) ∧ ∀ x, ∃ w : Sp O ⟶ P.A.left, w ≫ P.A.hom = 𝟙 _ ∧ w ≫ b₁ = spMap f₁ ≫ (t₁ x).left ∧ w ≫ b₂ = spMap f₂ ≫ (t₂ x).left := by
  obtain ⟨P, b₁, b₂, h₁, h₂, l₁, l₂, he, ht⟩ := h
  refine ⟨P, b₁, b₂, h₁, h₂, l₁, l₂, he, fun x => ?_⟩
  obtain ⟨w, w₁, w₂⟩ := ht x
  refine ⟨w, GlobalTheory.Poinc.Spread.endo_id f₁ hf _ ?_, w₁, w₂⟩
  have := Over.w (t₁ x)
  rw [Category.assoc, ← h₁.1.w, ← Category.assoc, w₁, Category.assoc, this]
  exact Category.comp_id _

theorem GlobalTheory.Poinc.Spread.main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) → ∀ (c₁ : X.Ω₁) (hc₁ : c₁ ≠ 0) (R'' : Subalgebra X.o₁ X.Ω₁) (fg₁ : R''.FG) (frac₁ : ∀ x : X.Ω₁, ∃ a ∈ R'', ∃ b ∈ R'', x = a / b) (hth₁ : ∀ x, c₁ * X.S.th x ∈ R'') (hev₁ : ∀ x k, c₁ * X.S.ev x k ∈ R'') (ρ'' : (X.S.rechart c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁).Real) (ε'' : Matrix (Fin 8) (Fin 8) ℤ → (ρ''.P.A ⟶ ρ''.P.A)), Same X.ρ ε ρ'' ε'' (fun x => x) (RingHom.id _) → R'' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₁ : R'' →+* PadicAlgCl p), (∀ a : R'', y₁ a = X.M.val (gPt p ≫ c.y) a) → ∀ (u : ρ'.UTest p y₀) (u' : ρ''.UTest p y₁), ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u'.A.L.pull a') ∧ (∀ b : X.S.Gam, ∃ (w : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt b).left ∧ x'.left ≫ u'.φ = spMap y₁ ≫ (ρ''.pt b).left) ∧ ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (w w₂ : Sp (PadicAlgCl p) ⟶ P₀.A.left), w ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ a ≫ u.φ = w ≫ a ≫ u.φ ≫ (ε' E).left → w₂ ≫ a' ≫ u'.φ = w ≫ a' ≫ u'.φ ≫ (ε'' E).left := by
  intro g n F W Z i X ε p _ z c c₀ hc R' fg frac hth hev ρ' ε' hS' hR' y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' ε'' hS'' hR'' y₁ hy₁ u u'
  set z' := (gPt p ≫ c.y) (closedPoint (PadicAlgCl p)) with hz'
  haveI : IsDedekindDomain X.o₁ := ArithBase.ded (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.O z') := GlobalTheory.Poinc.Spread.noeth X.o₁ X.Ω₁ X.M z'
  haveI : IsIntegrallyClosed (X.M.Z.presheaf.stalk z') := X.normal.isIntegrallyClosed_stalk z'
  haveI : IsIntegrallyClosed (X.M.O z') := IsIntegrallyClosed.of_equiv (X.M.stalkEquiv z')
  let ι' : R' →+* X.M.O z' := (Subalgebra.inclusion hR').toRingHom
  let ι'' : R'' →+* X.M.O z' := (Subalgebra.inclusion hR'').toRingHom
  have h0 := GlobalTheory.Poinc.SameComb.combine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS' hS''
  have h1 := GlobalTheory.Poinc.sameAt_of_generic (X.M.O z') X.Ω₁ _ _ _ _ _ _ ι' ι'' _ _ _ _ h0
  have hfr : ∀ o : X.M.O z', ∃ a b : R', ι' b ≠ 0 ∧ ι' b * o = ι' a := by
    intro o
    obtain ⟨a, ha, b, hb, e⟩ := frac (o : X.Ω₁)
    by_cases hb0 : b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      have : o = 0 := Subtype.ext (by simpa [hb0] using e)
      simp [this]
    · refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hb0 (congrArg Subtype.val h), Subtype.ext ?_⟩
      change b * (o : X.Ω₁) = a
      rw [e]; field_simp
  let v : X.M.O z' →+* PadicAlgCl p := RatModel.valHom (gPt p ≫ c.y) z' (RatModel.range_eq_singleton _ _)
  have e₀ : v.comp ι' = y₀ := RingHom.ext fun a => (hy₀ a).symm
  have e₁ : v.comp ι'' = y₁ := RingHom.ext fun a => (hy₁ a).symm
  obtain ⟨P₀, a, a', ha, ha', hL, hL', ht, hε⟩ := GlobalTheory.Poinc.Special.main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.Poinc.Spread.sec hfr h1) v u.yK u'.yK
    (u.fac.trans e₀.symm) (u'.fac.trans e₁.symm) u.A u'.A u.φ u'.φ u.cart u'.cart u.lb u'.lb
  refine ⟨P₀, a, a', ha, ha', hL, hL', fun b => ?_, fun E w w₂ hw hw₂ h => ?_⟩
  · obtain ⟨w, hw, h₁, h₂⟩ := ht b
    have q₁ : (w ≫ a) ≫ u.A.A.hom = jFK (R := u.V) (PadicAlgCl p) := by
      rw [Category.assoc, ha.1.w, ← Category.assoc, hw, Category.id_comp]
    have q₂ : (w ≫ a') ≫ u'.A.A.hom = jFK (R := u'.V) (PadicAlgCl p) := by
      rw [Category.assoc, ha'.1.w, ← Category.assoc, hw, Category.id_comp]
    refine ⟨w, Over.homMk (w ≫ a) q₁, Over.homMk (w ≫ a') q₂, hw, rfl, rfl, ?_, ?_⟩
    · simpa [e₀] using h₁
    · simpa [e₁] using h₂
  · exact hε E w w₂ hw hw₂ h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectRigidityIdentificationsEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelObject_rigidity_identifications_eq : ∀ (h M : ℕ), 3 ≤ M → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp (cycAway M)) (s' : S' ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s) (o : SiegPre h M (zetaAway M) s') (f : S' ⟶ S), Out.RelAmple c.A c.diag → ∀ (φ ψ : o.A.left ⟶ c.A.left) (φ₂ ψ₂ : (G2 o.A).left ⟶ (G2 c.A).left), IsGrpPullback o.A c.A f φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → (∀ a, (o.lev a).left ≫ φ = f ≫ (c.lev a).left) → IsGrpPullback o.A c.A f ψ → IsSquare ψ ψ₂ → LBIso o.P (c.P.pull ψ₂) → (∀ a, (o.lev a).left ≫ ψ = f ≫ (c.lev a).left) → φ = ψ := by
  first | (exact @GlobalTheory.SiegRigidCyc.eq_of_pullback) | (exact GlobalTheory.SiegRigidCyc.eq_of_pullback) | (intros; apply GlobalTheory.SiegRigidCyc.eq_of_pullback  <;> assumption)
end

